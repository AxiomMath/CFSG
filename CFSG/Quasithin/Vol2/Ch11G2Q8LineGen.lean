module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Gen
public import CFSG.Quasithin.Vol2.Ch11SecBFactsG2W
public import CFSG.Quasithin.Vol2.Ch11SecAKind
public import CFSG.Quasithin.Vol2.Ch11SecSCartanT3
public import CFSG.Quasithin.Vol2.Ch11G2Q8Real
public import CFSG.Quasithin.Vol2.Ch11SecA14Delta

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL)
open scoped IsMulCommutative

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem gmapG_mono {c : ↥(cayleyGroup K)} {S S' : Submodule K (Ix3 → K)} (h : S ≤ S') :
    gmapG c S ≤ gmapG c S' :=
  Submodule.map_mono h

theorem gmapG_one (S : Submodule K (Ix3 → K)) : gmapG 1 S = S := by
  ext x
  rw [mem_gmapG, inv_one, map_one]
  rfl

theorem gmapG_mul (c h : ↥(cayleyGroup K)) (S : Submodule K (Ix3 → K)) :
    gmapG (c * h) S = gmapG c (gmapG h S) := by
  ext x
  rw [mem_gmapG, mem_gmapG, mem_gmapG, _root_.mul_inv_rev, g2Act_mul_apply]

theorem gmapG_le_gmapG {c h : ↥(cayleyGroup K)} {S S' : Submodule K (Ix3 → K)}
    (hS : S ≤ gmapG h S') : gmapG c S ≤ gmapG (c * h) S' := by
  rw [gmapG_mul]
  exact gmapG_mono hS

theorem g2Act_swap12 (w : Ix3 → K) :
    g2Act (g2A swap12) w =
      q6 (w (.inl 0)) (w (.inl 2)) (w (.inl 1)) (w (.inr 0)) (w (.inr 2)) (w (.inr 1)) := by
  conv_lhs => rw [q6_eta w]
  have hA : ((swap12 : SL3 K) : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := rfl
  rw [g2Act_g2A, adjugate_swap12, hA]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6]

theorem swap12_mul_self : g2A (swap12 : SL3 K) * g2A swap12 = 1 := by
  refine cayley_ext_Q fun w => ?_
  rw [g2Act_mul_apply, g2Act_swap12, g2Act_swap12, map_one]
  funext k
  rcases k with k | k <;> fin_cases k <;> rfl

theorem swap12_inv : (g2A (swap12 : SL3 K))⁻¹ = g2A swap12 :=
  inv_eq_of_mul_eq_one_right swap12_mul_self

theorem stdF_one_le_swap : stdF K 1 ≤ gmapG (g2A swap12) (stdF K 2) := by
  intro x hx
  rw [mem_gmapG, swap12_inv, g2Act_swap12, mem_stdF, inF_q6_iff]
  have hx' : InF 1 x := hx
  conv at hx' => rw [q6_eta x]
  rw [inF_q6_iff] at hx'
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := hx'
  exact ⟨by omega, fun _ => h2 (by omega), fun _ => h1 (by omega), fun _ => h3 (by omega),
    fun _ => h5 (by omega), fun _ => h4 (by omega)⟩

theorem swap_le_stdF_three : gmapG (g2A swap12) (stdF K 2) ≤ stdF K 3 := by
  intro x hx
  rw [mem_gmapG, swap12_inv, g2Act_swap12, mem_stdF, inF_q6_iff] at hx
  rw [mem_stdF]
  conv => rw [q6_eta x]
  rw [inF_q6_iff]
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := hx
  exact ⟨by omega, fun _ => h2 (by omega), fun _ => h1 (by omega), fun _ => h3 (by omega),
    fun _ => h5 (by omega), by omega⟩

@[expose] noncomputable def rhoW {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {c₀ : K}
    (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H) :
    ↥(cayleyGroup K) →* MulAut W :=
  H.subtype.comp (rhoG hc0 hc1 π)

section Real

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}

theorem rhoW_conj_mem_stabW (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0)
    (hc1 : c₀ ≠ 1) (c : ↥(cayleyGroup K)) {k : ↥(cayleyGroup K)} (hk : k ∈ sl2E1 K) :
    rhoW hc0 hc1 π (c * k * c⁻¹) ∈
      Ch11.SecA.stabW (hf.pre (gmapG c (stdF K 2)).toAddSubgroup) := by
  change ((rhoG hc0 hc1 π (c * k * c⁻¹) : ↥H) : MulAut W) ∈ _
  rw [IsCoord.rhoG_mem_stabW_iff hf hc0 hc1 (hf.le_pre _), hf.img_pre]
  intro y
  change y ∈ gmapG c _ ↔ _ ∈ gmapG c _
  rw [mem_gmapG, mem_gmapG, conj_g2Act]
  exact (mem_stabQ.mp (sl2E1_le_stabQ hk)) _

end Real

theorem conjSubgroup_le_of_le {G : Type*} [Group G] {U V : Subgroup G} (hUV : U ≤ V) {y : G}
    (hy : y ∈ Subgroup.normalizer (V : Set G)) : conjSubgroup U y ≤ V := fun z hz =>
  (Subgroup.mem_normalizer_iff.mp hy z).mpr (hUV (mem_conjSubgroup_iff.mp hz))

theorem factG2LineGen_holds : SecB.FactG2LineGen := by
  intro G _ _ L V X T V₁ V₂ V₃ n hfl l hl
  obtain ⟨_, hnat⟩ := hfl.nat
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hfl.elem.2 w w.2)
  have hn := hfl.two_le
  have hLV := hfl.le_normalizer
  have h₁ : V₁ ≤ V := hfl.le₁₂.trans (hfl.le₂₃.trans hfl.le₃)
  have h₂ : V₂ ≤ V := hfl.le₂₃.trans hfl.le₃
  obtain ⟨K, _, _, hK, π, hπ⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(autOn L V),
        (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia (V := ↥V) (autOn L V) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf V) π := by
    rcases hnat with ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | hG2
    · obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
      have hbij : Function.Bijective π := ⟨hf.injective_nat, hf.onto⟩
      exact (SecA.kind_not_SL3_G2 KGNat.factG2DerivedOrder_holds hn
        ⟨K, inferInstance, inferInstance, hK,
          ⟨(MulEquiv.ofBijective π hbij).symm.trans
            (specialLinearGroupEquivStatedSL 3 K).symm⟩⟩ hfl.kind).elim
    · obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
      have hbij : Function.Bijective π := ⟨hf.injective_nat, hf.onto⟩
      exact (SecA.kind_not_Sp4_G2 KGNat.factG2DerivedOrder_holds hn
        ⟨K, inferInstance, inferInstance, hK, ⟨(MulEquiv.ofBijective π hbij).symm⟩⟩
        hfl.kind).elim
    · exact hG2
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  have hTL : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hfl.sylow le_sup_left (sup_le Subgroup.le_normalizer hfl.T_le_L)
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1
    (SecA.isSylowTwoOf_autOn hLV hTL)
  have hflag : ∀ {i : ℕ} {U : Subgroup G}, U ≤ V →
      V ⊓ Subgroup.centralizer (L : Set G) ≤ U →
      IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) U →
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex U = 2 ^ (n * i) →
      T ≤ Subgroup.normalizer (U : Set G) →
      U.subgroupOf V = hf.pre (gmapG g (stdF K i)).toAddSubgroup := by
    intro i U hUV hCU hst hidx hTU
    have hFW : SecA.IsFlagW (autOn L V) (autOn (T ⊓ L) V)
        ((Subgroup.centralizer (L : Set G)).subgroupOf V) (Nat.card K) i (U.subgroupOf V) := by
      refine ⟨fun z hz => hCU ⟨z.2, hz⟩, ?_, ?_, fun x hx => ?_⟩
      · have := (SecA.isEndStable_iff hLV _ U).mp hst
        rwa [SecA.inf_centralizer_subgroupOf] at this
      · rw [← SecA.inf_centralizer_subgroupOf, Subgroup.relIndex_subgroupOf hUV, hidx, hK,
          pow_mul]
      · obtain ⟨y, hy, hyV, rfl⟩ := SecA.mem_autOn_iff.mp hx
        exact (SecA.conjV_mem_stabW_iff hUV hyV).mpr (hTU hy.1)
    obtain ⟨S, hS, hc, hU⟩ := exists_eq_preG_of_isFlagW hsq hf hc0 hc1 hg hFW
    rw [hU, eq_stdF_of_card hS hc]
  have hV₁ := hflag (i := 1) h₁ hfl.cV_le hfl.stable₁ (by rw [hfl.index₁, mul_one])
    hfl.T_le_V₁
  have hV₂ := hflag (i := 2) h₂ (hfl.cV_le.trans hfl.le₁₂) hfl.stable₂ hfl.index₂ hfl.T_le_V₂
  have hV₃ := hflag (i := 3) hfl.le₃ (hfl.cV_le.trans (hfl.le₁₂.trans hfl.le₂₃)) hfl.stable₃
    hfl.index₃ hfl.T_le_V₃
  have hconj : ∀ {U : Subgroup G} {S : Submodule K (Ix3 → K)},
      U.subgroupOf V = hf.pre (gmapG g S).toAddSubgroup →
      ∀ (x : G) (hxL : x ∈ L) (a : ↥(cayleyGroup K)),
        ((rhoG hc0 hc1 π a : ↥(autOn L V)) : MulAut ↥V) = SecA.conjV V x (hLV hxL) →
        (conjSubgroup U x).subgroupOf V = hf.pre (gmapG (a⁻¹ * g) S).toAddSubgroup := by
    intro U S hU x hxL a ha
    ext w
    rw [Subgroup.mem_subgroupOf, mem_conjSubgroup_iff]
    change _ ↔ f w ∈ gmapG (a⁻¹ * g) S
    have h1 : x * (w : G) * x⁻¹ ∈ U ↔ SecA.conjV V x (hLV hxL) w ∈ U.subgroupOf V := by
      rw [Subgroup.mem_subgroupOf, SecA.conjV_apply_coe]
    rw [h1, hU]
    change f (SecA.conjV V x (hLV hxL) w) ∈ gmapG g S ↔ _
    rw [← ha, IsCoord.actG hf hc0 hc1, mem_gmapG, mem_gmapG, _root_.mul_inv_rev, inv_inv,
      g2Act_mul_apply]
  have hsurj : ∀ (y : G) (hy : y ∈ L), ∃ a : ↥(cayleyGroup K),
      ((rhoG hc0 hc1 π a : ↥(autOn L V)) : MulAut ↥V) = SecA.conjV V y (hLV hy) := by
    intro y hy
    obtain ⟨a, ha⟩ := (rhoG_bijective hf hc0 hc1).2
      ⟨SecA.conjV V y (hLV hy), SecA.conjV_mem_autOn hy _⟩
    exact ⟨a, by rw [ha]⟩
  obtain ⟨al, hal⟩ := hsurj l hl
  obtain ⟨x₂, hx₂L, _hx₂V, hx₂⟩ := SecA.mem_autOn_iff.mp
    (rhoG hc0 hc1 π (g * (g2A swap12)⁻¹ * g⁻¹ * al)).2
  have hI₁ := hconj hV₂ l hl al hal
  have hI₂ := hconj hV₂ x₂ hx₂L _ hx₂
  rw [show (g * (g2A swap12)⁻¹ * g⁻¹ * al)⁻¹ * g = al⁻¹ * g * g2A swap12 by group] at hI₂
  have hP₁ := hconj hV₁ l hl al hal
  have hP₃ := hconj hV₃ l hl al hal
  have hcond : ∀ x ∈ L, ∀ {h : ↥(cayleyGroup K)}, stdF K 1 ≤ gmapG h (stdF K 2) →
      gmapG h (stdF K 2) ≤ stdF K 3 →
      (conjSubgroup V₂ x).subgroupOf V =
        hf.pre (gmapG (al⁻¹ * g * h) (stdF K 2)).toAddSubgroup →
      conjSubgroup V₁ l ≤ conjSubgroup V₂ x ∧ conjSubgroup V₂ x ≤ conjSubgroup V₃ l := by
    intro x hx h h1 h3 hIx
    constructor
    · intro z hz
      have hzV := conjSubgroup_le_of_le h₁ (hLV hl) hz
      have hz' : f ⟨z, hzV⟩ ∈ gmapG (al⁻¹ * g) (stdF K 1) := by
        have h0 : (⟨z, hzV⟩ : ↥V) ∈ (conjSubgroup V₁ l).subgroupOf V := hz
        rw [hP₁] at h0
        exact h0
      have h0 : (⟨z, hzV⟩ : ↥V) ∈ (conjSubgroup V₂ x).subgroupOf V := by
        rw [hIx]
        exact gmapG_le_gmapG h1 hz'
      exact h0
    · intro z hz
      have hzV := conjSubgroup_le_of_le h₂ (hLV hx) hz
      have hz' : f ⟨z, hzV⟩ ∈ gmapG (al⁻¹ * g * h) (stdF K 2) := by
        have h0 : (⟨z, hzV⟩ : ↥V) ∈ (conjSubgroup V₂ x).subgroupOf V := hz
        rw [hIx] at h0
        exact h0
      have h0 : (⟨z, hzV⟩ : ↥V) ∈ (conjSubgroup V₃ l).subgroupOf V := by
        rw [hP₃]
        rw [gmapG_mul] at hz'
        exact gmapG_mono h3 hz'
      exact h0
  have hcond₁ := hcond l hl (h := 1) (by rw [gmapG_one]; exact stdF_mono (by norm_num))
    (by rw [gmapG_one]; exact stdF_mono (by norm_num)) (by rw [mul_one]; exact hI₁)
  have hcond₂ := hcond x₂ hx₂L stdF_one_le_swap swap_le_stdF_three hI₂
  set Y := ⨆ (x : G) (_ : x ∈ L ∧ conjSubgroup V₁ l ≤ conjSubgroup V₂ x ∧
      conjSubgroup V₂ x ≤ conjSubgroup V₃ l), LOf L (conjSubgroup V₂ x)
  have hYL : Y ≤ L := iSup₂_le fun x _ => (perfectCore_le _).trans inf_le_left
  have himg : ∀ (x : G) (hx : x ∈ L ∧ conjSubgroup V₁ l ≤ conjSubgroup V₂ x ∧
      conjSubgroup V₂ x ≤ conjSubgroup V₃ l) {d : ↥(cayleyGroup K)},
      (conjSubgroup V₂ x).subgroupOf V = hf.pre (gmapG d (stdF K 2)).toAddSubgroup →
      ∀ k ∈ sl2E1 K, rhoW hc0 hc1 π (d * k * d⁻¹) ∈ autOn Y V := by
    intro x hx d hId k hk
    have hU : conjSubgroup V₂ x ≤ V := conjSubgroup_le_of_le h₂ (hLV hx.1)
    have hKd : ⁅((sl2E1 K).map (MulAut.conj d).toMonoidHom).map (rhoW hc0 hc1 π),
        ((sl2E1 K).map (MulAut.conj d).toMonoidHom).map (rhoW hc0 hc1 π)⁆ =
        ((sl2E1 K).map (MulAut.conj d).toMonoidHom).map (rhoW hc0 hc1 π) := by
      rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, sl2E1_perfect hc0 hc1]
    have hmem : rhoW hc0 hc1 π (d * k * d⁻¹) ∈ autOn (LOf L (conjSubgroup V₂ x)) V := by
      rw [SecA.autOn_lOf hLV hU, hId]
      refine le_perfectCore_of_perfect ?_ hKd ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      rintro _ ⟨_, ⟨k', hk', rfl⟩, rfl⟩
      exact ⟨(rhoG hc0 hc1 π _).2, rhoW_conj_mem_stabW hf hc0 hc1 d hk'⟩
    exact SecS.autOn_mono (le_iSup₂ (f := fun x (_ : x ∈ L ∧ conjSubgroup V₁ l ≤
      conjSubgroup V₂ x ∧ conjSubgroup V₂ x ≤ conjSubgroup V₃ l) =>
        LOf L (conjSubgroup V₂ x)) x hx) hmem
  have key : ∀ b ∈ genE12 K, rhoW hc0 hc1 π ((al⁻¹ * g) * b * (al⁻¹ * g)⁻¹) ∈ autOn Y V := by
    intro b hb
    rw [genE12] at hb
    induction hb using Subgroup.closure_induction with
    | mem b hb =>
      rcases hb with hb | ⟨b', hb', rfl⟩
      · exact himg l ⟨hl, hcond₁⟩ hI₁ b (Subgroup.subset_closure hb)
      · have := himg x₂ ⟨hx₂L, hcond₂⟩ hI₂ b' (Subgroup.subset_closure hb')
        rwa [show al⁻¹ * g * g2A swap12 * b' * (al⁻¹ * g * g2A swap12)⁻¹ =
          al⁻¹ * g * (g2A swap12 * b' * (g2A swap12)⁻¹) * (al⁻¹ * g)⁻¹ by group] at this
    | one => rw [mul_one, mul_inv_cancel, map_one]; exact (autOn Y V).one_mem
    | mul b b' _ _ hb hb' =>
      rw [show al⁻¹ * g * (b * b') * (al⁻¹ * g)⁻¹ =
        (al⁻¹ * g * b * (al⁻¹ * g)⁻¹) * (al⁻¹ * g * b' * (al⁻¹ * g)⁻¹) by group, map_mul]
      exact (autOn Y V).mul_mem hb hb'
    | inv b _ hb =>
      rw [show al⁻¹ * g * b⁻¹ * (al⁻¹ * g)⁻¹ = (al⁻¹ * g * b * (al⁻¹ * g)⁻¹)⁻¹ by group,
        map_inv]
      exact (autOn Y V).inv_mem hb
  have hall : ∀ a : ↥(cayleyGroup K), rhoW hc0 hc1 π a ∈ autOn Y V := by
    intro a
    have := key ((al⁻¹ * g)⁻¹ * a * (al⁻¹ * g))
      (by rw [genE12_eq_top]; exact Subgroup.mem_top _)
    rwa [show al⁻¹ * g * ((al⁻¹ * g)⁻¹ * a * (al⁻¹ * g)) * (al⁻¹ * g)⁻¹ = a by group] at this
  intro y hy
  obtain ⟨a, ha⟩ := hsurj y hy
  have hya : SecA.conjV V y (hLV hy) ∈ autOn Y V := by
    rw [← ha]
    exact hall a
  obtain ⟨y', hy'Y, hy'V, hyy'⟩ := SecA.mem_autOn_iff.mp hya
  have hmem : y'⁻¹ * y ∈ L ⊓ Subgroup.centralizer (V : Set G) :=
    ⟨L.mul_mem (L.inv_mem (hYL hy'Y)) hy, SecS.inv_mul_mem_centralizer hyy'.symm⟩
  rw [show y = y' * (y'⁻¹ * y) by group]
  exact Subgroup.mul_mem_sup hy'Y hmem

end CFSG.Quasithin.Vol2.Ch11.G2Q8
