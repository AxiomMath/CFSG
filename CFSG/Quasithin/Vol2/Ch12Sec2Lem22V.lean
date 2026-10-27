module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22U
public import CFSG.Quasithin.Vol2.KGFactBorelThree

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem22

section Restrict

variable {A : Type*} [Group A]

@[expose] def stabSub (B : Subgroup A) : Subgroup (MulAut A) where
  carrier := {g | ∀ a, a ∈ B ↔ g a ∈ B}
  one_mem' := fun a => Iff.rfl
  mul_mem' := fun {g g'} hg hg' a => (hg' a).trans (hg (g' a))
  inv_mem' := fun {g} hg a => by
    have := hg (g⁻¹ a)
    simp only [MulAut.apply_inv_self] at this
    exact this.symm

@[expose] def restrictHom (B : Subgroup A) : ↥(stabSub B) →* MulAut ↥B where
  toFun g :=
    { toFun := fun b => ⟨(g : MulAut A) b, (g.2 b).mp b.2⟩
      invFun := fun b => ⟨(g : MulAut A)⁻¹ b, (g⁻¹.2 b).mp b.2⟩
      left_inv := fun b => Subtype.ext (by simp)
      right_inv := fun b => Subtype.ext (by simp)
      map_mul' := fun b b' => Subtype.ext (by simp) }
  map_one' := by ext b; rfl
  map_mul' := fun g g' => by ext b; rfl

theorem restrictHom_apply (B : Subgroup A) (g : ↥(stabSub B)) (b : ↥B) :
    ((restrictHom B g b : ↥B) : A) = (g : MulAut A) b := rfl

variable [Finite A]

theorem card_le_mul_card_restrict {B : Subgroup A}
    (hB2 : B.index = 2) {R : Subgroup (MulAut A)} (hRB : R ≤ stabSub B) :
    Nat.card R ≤ Nat.card B * Nat.card ((R.subgroupOf (stabSub B)).map (restrictHom B)) := by
  set St := stabSub B with hSt
  let φ : ↥(R.subgroupOf St) →* MulAut ↥B := (restrictHom B).comp (R.subgroupOf St).subtype
  have hcardR : Nat.card R = Nat.card ↥(R.subgroupOf St) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRB).toEquiv).symm
  have hrange : φ.range = (R.subgroupOf St).map (restrictHom B) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hBtop : B ≠ ⊤ := fun h0 => by rw [h0, Subgroup.index_top] at hB2; norm_num at hB2
  obtain ⟨a₀, -, ha₀⟩ := IsConcreteLE.not_le_iff_exists.mp (fun h0 => hBtop (top_le_iff.mp h0))
  have hmemB : ∀ g ∈ St, (g : MulAut A) a₀ * a₀⁻¹ ∈ B := by
    intro g hg
    have h1 : (g : MulAut A) a₀ ∉ B := fun h0 => ha₀ ((hg a₀).mpr h0)
    rw [Subgroup.mul_mem_iff_of_index_two hB2]
    exact iff_of_false h1 (fun h0 => ha₀ (by simpa using B.inv_mem h0))
  have hker : Nat.card φ.ker ≤ Nat.card B := by
    refine Nat.card_le_card_of_injective
      (fun k : ↥φ.ker => (⟨(((k : ↥(R.subgroupOf St)) : ↥St) : MulAut A) a₀ * a₀⁻¹,
        hmemB _ (k : ↥(R.subgroupOf St)).1.2⟩ : ↥B)) ?_
    intro k k' h0
    have h1 : (((k : ↥(R.subgroupOf St)) : ↥St) : MulAut A) a₀ =
        (((k' : ↥(R.subgroupOf St)) : ↥St) : MulAut A) a₀ := by
      have := congrArg Subtype.val h0
      simpa using this
    have hkB : ∀ (k : ↥φ.ker) (b : A), b ∈ B →
        (((k : ↥(R.subgroupOf St)) : ↥St) : MulAut A) b = b := by
      intro k b hb
      have h2 := congrArg (fun α : MulAut ↥B => ((α ⟨b, hb⟩ : ↥B) : A)) k.2
      simpa [φ, restrictHom_apply] using h2
    have hgen : Subgroup.closure ((B : Set A) ∪ {a₀}) = ⊤ := by
      have hlt : B < Subgroup.closure ((B : Set A) ∪ {a₀}) := lt_of_le_of_ne
        (fun b hb => Subgroup.subset_closure (Or.inl hb))
        fun h0 => ha₀ (h0 ▸ Subgroup.subset_closure (Or.inr rfl))
      have h3 := Subgroup.index_dvd_of_le hlt.le
      rw [hB2] at h3
      have h4 : (Subgroup.closure ((B : Set A) ∪ {a₀})).index ≠ 2 := by
        intro h5
        have h6 := Subgroup.relIndex_mul_index hlt.le
        rw [hB2, h5] at h6
        have h7 : B.relIndex (Subgroup.closure ((B : Set A) ∪ {a₀})) = 1 := by omega
        exact (ne_of_lt hlt) (Subgroup.relIndex_eq_one.mp h7 |> le_antisymm hlt.le)
      have h8 : (Subgroup.closure ((B : Set A) ∪ {a₀})).index = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h9 | h9
        · exact h9
        · exact absurd h9 h4
      exact Subgroup.index_eq_one.mp h8
    have hg := eq_one_of_fix_closure
      (g := ((((k : ↥(R.subgroupOf St)) : ↥St) : MulAut A))⁻¹ *
        (((k' : ↥(R.subgroupOf St)) : ↥St) : MulAut A)) hgen (by
      intro s hs
      show ((((k : ↥(R.subgroupOf St)) : ↥St) : MulAut A))⁻¹
        ((((k' : ↥(R.subgroupOf St)) : ↥St) : MulAut A) s) = s
      rcases hs with hs | hs
      · rw [hkB k' s hs]
        calc ((((k : ↥(R.subgroupOf St)) : ↥St) : MulAut A))⁻¹ s
            = ((((k : ↥(R.subgroupOf St)) : ↥St) : MulAut A))⁻¹
              ((((k : ↥(R.subgroupOf St)) : ↥St) : MulAut A) s) := by rw [hkB k s hs]
          _ = s := by simp
      · rw [Set.mem_singleton_iff] at hs
        rw [hs, ← h1]
        simp)
    rw [inv_mul_eq_one] at hg
    exact Subtype.ext (Subtype.ext (Subtype.ext hg))
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hrange] at h1
  rw [hcardR, ← h1]
  exact Nat.mul_le_mul_right _ hker


end Restrict

variable {G : Type} [Group G] [Finite G]

theorem autOn_facts (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hyp : Hyp1223 G T L V) (hC : Concl12_2_20 T L V n)
    (hpre : Pre12_2_21 T L V H P U I h p)
    (hΦV : (frattini ↥P).map P.subtype ≤ Subgroup.normalizer (V : Set G)) :
    IsSylowTwoOf (autOn T V) ⊤ ∧ IsPGroup p ↥(autOn ((frattini ↥P).map P.subtype) V) ∧
      ∀ s ∈ autOn T V, ∀ x ∈ autOn ((frattini ↥P).map P.subtype) V,
        ∃ x' ∈ autOn ((frattini ↥P).map P.subtype) V, ∃ s' ∈ autOn T V, s * x = x' * s' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hHs, hsol, hp, hp2, hPp, hPH, hPi, -, -, hhP, hhM, -⟩ := hpre
  set Q := pCoreOf 2 H with hQ
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  have hh1 : h ≠ 1 := fun h1 => hhM (h1 ▸ Subgroup.one_mem _)
  have hP1 : P ≠ ⊥ := fun h0 => hh1 (by rw [h0] at hhP; exact Subgroup.mem_bot.mp hhP)
  have hΦP : Φ ≤ P := frattini_map_le P
  obtain ⟨-, -, hall⟩ := ((h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).resolve_left
    hyp.notAlt) L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨-, hTV, -, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hmin := Lem7.minParabolic h331 hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hQT : Q ≤ T := pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hOH : Q ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hHO : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hfr : ∀ g ∈ H, ∃ q ∈ Q, q * g ∈ Subgroup.normalizer (P : Set G) := fun g hg =>
    exists_mul_mem_normalizer h331 hyp hHs hsol hp hp2 hPp hPH hPi hP1 hg
  have hHΦ := le_normalizer_frattini_sup hPH hHO hOH hfr
  obtain ⟨-, -, hautL, -, -⟩ := hC
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hTLT : IsSylowTwoOf T (L ⊔ T) := isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_sup_right
  refine ⟨?_, ?_, ?_⟩
  · have h1 := isSylowTwoOf_map_hom (isSylowTwoOf_subgroupOf_of_le hLTV hTLT) (conjAct V)
    have h2 : autOn (L ⊔ T) V = ⊤ := by
      rw [eq_top_iff, ← hautL]
      exact Subgroup.map_mono (Subgroup.comap_mono le_sup_left)
    have h3 : ((L ⊔ T).subgroupOf (Subgroup.normalizer (V : Set G))).map (conjAct V) = ⊤ := h2
    rw [h3] at h1
    exact h1
  · have h1 : IsPGroup p ↥(Φ.subgroupOf (Subgroup.normalizer (V : Set G))) :=
      (hPp.to_le hΦP).of_equiv (Subgroup.subgroupOfEquivOfLe hΦV).symm
    exact h1.map (conjAct V)
  · rintro _ ⟨t, ht, rfl⟩ _ ⟨f, hf, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ht hf
    have htf : (t : G) * f * (t : G)⁻¹ ∈ Φ ⊔ Q :=
      (Subgroup.mem_normalizer_iff.mp (hHΦ (hTH ht)) f).mp (Subgroup.mem_sup_left hf)
    have hΦQ : Φ ≤ Subgroup.normalizer (Q : Set G) := hΦP.trans (hPH.trans hHO)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hΦQ] at htf
    obtain ⟨f', hf', q, hq, hfq⟩ := htf
    have hfq' : f' * q = (t : G) * f * (t : G)⁻¹ := hfq
    have hqt : q * t ∈ T := T.mul_mem (hQT hq) ht
    refine ⟨conjAct V ⟨f', hΦV hf'⟩, ⟨⟨f', hΦV hf'⟩, Subgroup.mem_subgroupOf.mpr hf', rfl⟩,
      conjAct V ⟨q * t, hTV hqt⟩, ⟨⟨q * t, hTV hqt⟩, Subgroup.mem_subgroupOf.mpr hqt, rfl⟩, ?_⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (t : G) * f = ((t : G) * f * (t : G)⁻¹) * t := by group
      _ = f' * q * t := by rw [← hfq']
      _ = f' * (q * t) := by group

theorem card_mulAut_of_card_32 {W : Type*} [Group W] [Finite W] (hWc : ∀ a b : W, a * b = b * a)
    (hW2 : ∀ a : W, a ^ 2 = 1) (hW32 : Nat.card W = 2 ^ 5) :
    Nat.card (MulAut W) = 2 ^ 10 * 9765 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hWc hW2 hW32
  rw [Nat.card_congr (CFSG.SectionRank.Ccomm.elemAutEquivGL e₀).toEquiv, Matrix.card_GL_field 5,
    ZMod.card]
  decide

theorem card_sylow_two_of {X : Type*} [Group X] [Finite X] {S : Subgroup X}
    (hS : IsSylowTwoOf S ⊤) (hX : Nat.card X = 2 ^ 10 * 9765) : Nat.card S = 2 ^ 10 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hS2, hidx⟩ := hS
  obtain ⟨k, hk⟩ := hS2.exists_card_eq
  have hi : ¬ 2 ∣ S.index := by
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at hidx
  have h1 := Subgroup.card_mul_index S
  rw [hk, hX] at h1
  have hk10 : k ≤ 10 := by
    by_contra h0
    push Not at h0
    have h2 : 2 ^ 11 ∣ 2 ^ 10 * 9765 := by
      rw [← h1]
      exact Dvd.dvd.mul_right (Nat.pow_dvd_pow 2 h0) _
    norm_num at h2
  rw [hk]
  interval_cases k <;> omega


theorem false_of_five_fpf (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) {T L V H P U I : Subgroup G}
    {h : G} (hyp : Hyp1223 G T L V) (hC : Concl12_2_20 T L V 5)
    (hpre : Pre12_2_21 T L V H P U I h 3) (hUO : U ≤ pCoreOf 2 H) (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hΦ3 : Nat.card ((frattini ↥P).map P.subtype) = 3)
    (hΦV : (frattini ↥P).map P.subtype ≤ Subgroup.normalizer (V : Set G))
    (hfpf : (V ⊓ pCoreOf 2 H) ⊓
      Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) = ⊥) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hS, hXp, hSX⟩ := autOn_facts h331 h1222 hyp hC hpre hΦV
  have hVO := Lem21.not_le_pCoreOf_of_pre hpre
  obtain ⟨hHs, -, -, -, -, hPH, -, -, -, -, -, -, -, -, -, -, -, -, hidx, -, -⟩ := hpre
  set Q := pCoreOf 2 H with hQ
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  set S := autOn T V with hSdef
  set X := autOn Φ V with hXdef
  obtain ⟨-, hcardV, -, ⟨hcommV, -⟩, -⟩ := hC
  obtain ⟨-, -, hall⟩ := ((h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).resolve_left
    hyp.notAlt) L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨-, hTV, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hV2' := sq_eq_one_of_hyp1223 hyp hred
  have hcV : ∀ a b : ↥V, a * b = b * a := fun a b => hcommV.is_comm.comm a b
  have hScard : Nat.card S = 2 ^ 10 :=
    card_sylow_two_of hS (card_mulAut_of_card_32 hcV hV2' hcardV)
  have hmin := Lem7.minParabolic h331 hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hHO : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hΦP : Φ ≤ P := frattini_map_le P
  set V₀ := (V ⊓ Q).subgroupOf V with hV₀def
  have hUV : U ⊓ V = Q ⊓ V :=
    ((Lem21.eq_or_le_of_relIndex_eq_two (inf_le_inf_right V hUO) inf_le_right
      hidx).resolve_right fun hle => hVO (hle.trans inf_le_left)).symm
  have hV₀idx : V₀.index = 2 := by
    have h1 : (V ⊓ Q).relIndex V = 2 := by rw [inf_comm, ← hUV]; exact hidx
    exact h1
  have hV₀card : Nat.card V₀ = 16 := by
    have h1 := Subgroup.card_mul_index V₀
    rw [hV₀idx, Nat.card_congr (Equiv.refl ↥V), hcardV] at h1
    omega
  have hV₀c : ∀ a b : ↥V₀, a * b = b * a := fun a b => Subtype.ext (hcV a b)
  have hΦ1 : Φ ≠ ⊥ := fun h0 => by rw [h0, Subgroup.card_bot] at hΦ3; norm_num at hΦ3
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hΦ1
  have hz1' : z ≠ 1 := fun h0 => hz1 (Subtype.ext h0)
  have hz3 : z ^ 3 = 1 := hexp z (hΦP hz)
  have hzp : Subgroup.zpowers z = Φ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
    rw [hΦ3, Nat.card_zpowers]
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hz3) with h4 | h4
    · exact absurd (orderOf_eq_one_iff.mp h4) hz1'
    · rw [h4]
  set zb := conjAct V ⟨z, hΦV hz⟩ with hzb
  have hzbX : zb ∈ X := ⟨⟨z, hΦV hz⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
  have hstab : ∀ g (hg : g ∈ Subgroup.normalizer (V : Set G)),
      g ∈ Subgroup.normalizer (Q : Set G) → conjAct V ⟨g, hg⟩ ∈ stabSub V₀ := by
    intro g hg hgQ w
    rw [hV₀def, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    show (w : G) ∈ V ⊓ Q ↔ g * w * g⁻¹ ∈ V ⊓ Q
    constructor
    · intro hw
      exact ⟨(Subgroup.mem_normalizer_iff.mp hg w).mp hw.1,
        (Subgroup.mem_normalizer_iff.mp hgQ w).mp hw.2⟩
    · intro hw
      exact ⟨w.2, (Subgroup.mem_normalizer_iff.mp hgQ w).mpr hw.2⟩
  have hSst : S ≤ stabSub V₀ := by
    rintro _ ⟨⟨t, htN⟩, ht, rfl⟩
    exact hstab t htN (hHO (hTH (Subgroup.mem_subgroupOf.mp ht)))
  have hzbst : zb ∈ stabSub V₀ := hstab z (hΦV hz) (hHO (hPH (hΦP hz)))
  set z' := restrictHom V₀ ⟨zb, hzbst⟩ with hz'
  have hz'3 : z' ^ 3 = 1 := by
    have h1 : (⟨zb, hzbst⟩ : ↥(stabSub V₀)) ^ 3 = 1 := by
      apply Subtype.ext
      show zb ^ 3 = 1
      rw [hzb, ← map_pow]
      have h2 : (⟨z, hΦV hz⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 3 = 1 :=
        Subtype.ext (by simpa using hz3)
      rw [h2, map_one]
    rw [hz', ← map_pow, h1, map_one]
  have hz'fix : ∀ w : ↥V₀, z' w = w → w = 1 := by
    intro w hw
    have h1 : z * ((w : ↥V) : G) * z⁻¹ = ((w : ↥V) : G) := by
      have := congrArg (fun x : ↥V₀ => ((x : ↥V) : G)) hw
      exact this
    have hwmem : ((w : ↥V) : G) ∈ (V ⊓ Q) ⊓ Subgroup.centralizer (Φ : Set G) := by
      refine ⟨Subgroup.mem_subgroupOf.mp w.2, Subgroup.mem_centralizer_iff.mpr fun f hf => ?_⟩
      rw [← hzp] at hf
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
      have hzw : z * ((w : ↥V) : G) = ((w : ↥V) : G) * z := by
        calc z * ((w : ↥V) : G) = (z * ((w : ↥V) : G) * z⁻¹) * z := by group
          _ = ((w : ↥V) : G) * z := by rw [h1]
      exact (Commute.zpow_left hzw k)
    rw [hfpf, Subgroup.mem_bot] at hwmem
    exact Subtype.ext (Subtype.ext hwmem)
  have hXS : ∀ y ∈ X, y ∈ S → y = 1 := fun y hyX hyS =>
    eq_one_of_mem_of_mem Nat.prime_three (by norm_num) hXp hS.2.1 hyX hyS
  have hXcard : Nat.card X = 3 := by
    have h1 : Nat.card X ∣ 3 := by
      rw [← hΦ3]
      have h2 := Subgroup.card_map_dvd (Φ.subgroupOf (Subgroup.normalizer (V : Set G)))
        (conjAct V)
      have h3 : Nat.card ↥(Φ.subgroupOf (Subgroup.normalizer (V : Set G))) = Nat.card Φ :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΦV).toEquiv
      rw [h3] at h2
      exact h2
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h4 | h4
    · exfalso
      have h5 := Subgroup.card_eq_one.mp h4
      have hzb1 : zb = 1 := by
        have := hzbX
        rw [h5, Subgroup.mem_bot] at this
        exact this
      have hV₀1 : V₀ ≠ ⊥ := fun h0 => by
        rw [h0, Subgroup.card_bot] at hV₀card
        norm_num at hV₀card
      obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV₀1
      apply hw1
      apply hz'fix
      apply Subtype.ext
      show zb (w : ↥V) = w
      rw [hzb1]
      rfl
    · exact h4
  set K := mulSub X S hSX with hK
  have hKcard : Nat.card K = 3 * 2 ^ 10 := by
    rw [hK, card_mulSub hSX hXS, hXcard, hScard]
  have hSK : S ≤ K := fun s hs => ⟨1, X.one_mem, s, hs, by rw [one_mul]⟩
  have hzbK : zb ∈ K := ⟨zb, hzbX, 1, S.one_mem, by rw [mul_one]⟩
  set S' := S.subgroupOf K with hS'
  have hS'card : Nat.card S' = 2 ^ 10 := by
    rw [hS', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv, hScard]
  have hS'idx : S'.index = 3 := by
    have h1 := Subgroup.card_mul_index S'
    rw [hS'card, Nat.card_congr (Equiv.refl ↥K), hKcard] at h1
    omega
  set R₀ := S'.normalCore with hR₀
  have hR₀idx : R₀.index ∣ 6 := by
    have h1 := Subgroup.index_normalCore_dvd_factorial_index S'
    rw [hS'idx] at h1
    exact h1
  have hR₀card : 2 ^ 9 ≤ Nat.card R₀ := by
    have h1 := Subgroup.card_mul_index R₀
    rw [Nat.card_congr (Equiv.refl ↥K), hKcard] at h1
    have h2 := Nat.le_of_dvd (by norm_num) hR₀idx
    have h3 : 0 < R₀.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    nlinarith
  set R := R₀.map K.subtype with hR
  have hRcard : Nat.card R = Nat.card R₀ :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hRS : R ≤ S := by
    rintro _ ⟨r, hr, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (Subgroup.normalCore_le S' hr)
  have hR2 : IsPGroup 2 ↥R := hS.2.1.to_le hRS
  have hRst : R ≤ stabSub V₀ := hRS.trans hSst
  have hzbR : ∀ r ∈ R, zb⁻¹ * r * zb ∈ R := by
    rintro _ ⟨r, hr, rfl⟩
    have h1 := (Subgroup.normalCore_normal S').conj_mem r hr (⟨zb, hzbK⟩ : ↥K)⁻¹
    refine ⟨_, h1, ?_⟩
    simp
  set Y := (R.subgroupOf (stabSub V₀)).map (restrictHom V₀) with hY
  have hY2 : IsPGroup 2 ↥Y :=
    (hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRst).symm).map (restrictHom V₀)
  have hz'Y : ∀ y ∈ Y, z'⁻¹ * y * z' ∈ Y := by
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨(⟨zb, hzbst⟩ : ↥(stabSub V₀))⁻¹ * r * ⟨zb, hzbst⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (hzbR _ (Subgroup.mem_subgroupOf.mp hr))
    · rw [hz', map_mul, map_mul, map_inv]
  have hYcard := card_le_sixteen_of_fpf hV₀c hV₀card hz'3 hz'fix hY2 hz'Y
  have hRle := card_le_mul_card_restrict hV₀idx hRst
  rw [hV₀card] at hRle
  have : Nat.card R ≤ 16 * 16 := hRle.trans (Nat.mul_le_mul_left _ hYcard)
  rw [hRcard] at this
  omega

end Lem22

end CFSG.Quasithin.H13
