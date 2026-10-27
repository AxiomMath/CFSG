module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem335
public import CFSG.Quasithin.Vol2.Ch3Sec3UniqueMax
public import CFSG.Quasithin.Vol2.Ch5Sec1Facts
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328
public import CFSG.Quasithin.Background.InternalSecB51

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative Pointwise

@[expose] def Stmt3_3_8One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ¬ T ≤ Subgroup.normalizer (L : Set G) →
      ∃ _ : IsMulCommutative ↥(vPlus L T), Case3_3_8_one T L

@[expose] def Stmt3_3_8OneGroup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ¬ T ≤ Subgroup.normalizer (L : Set G) →
      ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) ∧ mPlus L T = L ⊔ CFSG.conjugate L t ∧
        (∀ a ∈ autOn L (vPlus L T), ∀ b ∈ autOn (CFSG.conjugate L t) (vPlus L T),
          a * b = b * a) ∧
        autOn L (vPlus L T) ⊓ autOn (CFSG.conjugate L t) (vPlus L T) = ⊥ ∧
        ((∃ n : ℕ, LieModel ↥(autOn L (vPlus L T)) .PSL 2 2 n) ∨
          IsPSL 3 2 1 ↥(autOn L (vPlus L T)))

theorem stmt3_3_8OneGroup_of (h : Stmt3_3_8One) : Stmt3_3_8OneGroup := by
  intro G _ _ T M L D hyp hT
  obtain ⟨_, t, ht, htn, hMp, hc, hinf, hty, -⟩ := h G T M L D hyp hT
  exact ⟨t, ht, htn, hMp, hc, hinf, hty⟩

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

omit [Finite G] in
theorem autOn_map_conj {V X : Subgroup G} {u : G} (hu : u ∈ Subgroup.normalizer (V : Set G)) :
    autOn (X.map (MulAut.conj u).toMonoidHom) V =
      (autOn X V).map (MulAut.conj (conjAct V ⟨u, hu⟩)).toMonoidHom :=
  CFSG.Quasithin.AutOn.autOn_map_conj hu

namespace Hyp331

theorem pCoreOf_sup_D_ne_bot (h : Hyp331 G T M L D) : pCoreOf 2 (T ⊔ D) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  apply h.toSetup331.T_ne_bot
  refine le_bot_iff.mp (hbot ▸ CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_left
    (sup_le Subgroup.le_normalizer h.DN) h.sylow.1)

theorem pCoreOf_sup_ne_bot (h : Hyp331 G T M L D) (h311 : Theorem311Stmt) {H : Subgroup G}
    (hH : InH T H) (hu : ∃ K : Subgroup G, IsUniqueMaxOver H T K) : pCoreOf 2 (H ⊔ D) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R₀, hR₀, hR₀T, hN⟩ := h311 G T h.simple h.nonabelian h.qtke h.sylow (T ⊔ D) H T
    ⟨le_sup_left, h.pCoreOf_sup_D_ne_bot⟩ hH hu h.toSetup331.T_ne_bot le_rfl
    (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right) (sup_le Subgroup.le_normalizer h.DN)
  intro hbot
  apply hR₀
  refine le_bot_iff.mp (hbot ▸ CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hR₀T.trans (hH.1.trans le_sup_left)) ?_ (h.sylow.1.to_le hR₀T))
  exact sup_le (le_sup_right.trans hN) ((le_sup_right.trans le_sup_left).trans hN)

theorem not_isUniqueMaxOver
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h311 : Theorem311Stmt) : ¬ ∃ K : Subgroup G, IsUniqueMaxOver (L ⊔ T) T K := fun hu =>
  h.pCoreOf_sup_ne_bot h311 ⟨le_sup_right, h.toSetup331.pCoreOf_ne_bot⟩ hu
    (h.pCoreOf_sup_eq_bot h38 h39)

theorem autOn_data (h : Hyp331 G T M L D) :
    autOn (mPlus L T) (vPlus L T) ≤ autOn (L ⊔ T) (vPlus L T) ∧
      autOn (L ⊔ T) (vPlus L T) ≤
        Subgroup.normalizer (autOn (mPlus L T) (vPlus L T) : Set (MulAut ↥(vPlus L T))) ∧
      (∀ x ∈ autOn (L ⊔ T) (vPlus L T), ∃ e : ℕ, x ^ 2 ^ e ∈ autOn (mPlus L T) (vPlus L T)) ∧
      IsSylowTwoOf (autOn T (vPlus L T)) (autOn (L ⊔ T) (vPlus L T)) := by
  have hHV : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) := (vPlus_reduced h.toSetup331).2.2.2.1
  have hMH : mPlus L T ≤ L ⊔ T := by
    rw [← conjClosure_sup_eq]
    exact le_sup_left
  have hHM : L ⊔ T ≤ Subgroup.normalizer (mPlus L T : Set G) := sup_le_normalizer_conjClosure L T
  have hn := InternalSec.autOn_normal_of (U := vPlus L T) hHM
  refine ⟨InternalSec.autOn_le_autOn_of_le hMH, fun x hx => ?_, ?_,
    CFSG.QuasithinUnique.Setup.isSylowTwoOf_autOn h.toSetup331.isSylowTwoOf hHV⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · exact hn x hx k
    · intro hk
      have := hn x⁻¹ ((autOn (L ⊔ T) (vPlus L T)).inv_mem hx) _ hk
      simpa [mul_assoc] using this
  · refine InternalSec.autOn_two_of (hMH.trans hHV) fun y hy => ?_
    rw [← conjClosure_sup_eq] at hy
    obtain ⟨e, he⟩ := InternalSec.two_of_sup h.sylow.1 (le_normalizer_conjClosure_right L T) y hy
    exact ⟨e, Subgroup.mem_sup_left he⟩

theorem not_lieModel_psl2
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h311 : Theorem311Stmt) (hRO : RankOneListedFacts.{0}) (n : ℕ) :
    ¬ LieModel ↥(autOn (mPlus L T) (vPlus L T)) .PSL 2 2 n := by
  intro hL
  have hn : 1 ≤ n := by
    rcases hL with ⟨-, ⟨-, hf, -⟩, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hf
    all_goals exact absurd h0 (by norm_num)
  have hK := hRO _ (isRankOneListed_of_lieModel hn hL)
  obtain ⟨hKX, hXK, h2, hS⟩ := h.autOn_data
  obtain ⟨hne, hmax⟩ := le_normalizer_of_rankOne hKX hXK h2 hS hK
  have hC := (h.centralizer_vPlus h38 h39).2.2
  exact h.not_isUniqueMaxOver h38 h39 h311
    (exists_isUniqueMaxOver_of_autOn (vPlus_reduced h.toSetup331).2.2.2.1 le_sup_right
      (pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf) hC inf_le_left hne
      (le_inf hS.1 fun s hs => mem_normalizer_inf (Subgroup.le_normalizer hs) (hXK (hS.1 hs)))
      fun Y hSY hYX hYne => hmax Y hSY hYX hYne)

theorem map_conj_mem
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat)
    (hT : ¬ T ≤ Subgroup.normalizer (L : Set G)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {u : G} (hu : u ∈ L ⊔ T) :
    L.map (MulAut.conj u).toMonoidHom = L ∨
      L.map (MulAut.conj u).toMonoidHom = CFSG.conjugate L t := by
  rcases lemma_1_2_1_three h.qtke h.simple h.nonabelian
      (a37ForSQTK_of_cat CFSG.QuasithinUnique.Vol2Native.a37ForSQTKCat_proved)
      (a38ForSQTK_of_cat h38) h.toSetup331.pCoreOf_ne_bot h.toSetup331.mem_cComp with
    hL | ⟨h2, -⟩
  · exact absurd (le_sup_right.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hL)) hT
  obtain ⟨x, y, hxy, hset⟩ := Set.ncard_eq_two.mp h2
  have hmem : ∀ v ∈ L ⊔ T, L.map (MulAut.conj v).toMonoidHom ∈ ({x, y} : Set (Subgroup G)) :=
    fun v hv => hset ▸ ⟨v, hv, rfl⟩
  have hL1 : L ∈ ({x, y} : Set (Subgroup G)) := by
    have := hmem 1 (Subgroup.one_mem _)
    have e1 : L.map (MulAut.conj (1 : G)).toMonoidHom = L := by
      ext z
      simp
    rwa [e1] at this
  have hLt : CFSG.conjugate L t ∈ ({x, y} : Set (Subgroup G)) :=
    hmem t⁻¹ ((L ⊔ T).inv_mem (Subgroup.mem_sup_right ht))
  have hne : L ≠ CFSG.conjugate L t := by
    intro heq
    apply htn
    have h1 : t⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      Ch3Sec3.mem_normalizer_of_map_conj_eq heq.symm
    simpa using inv_mem h1
  have hu' := hmem u hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL1 hLt hu'
  rcases hL1 with h1 | h1 <;> rcases hLt with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · rcases hu' with h3 | h3
    · exact Or.inl (h3.trans h1.symm)
    · exact Or.inr (h3.trans h2.symm)
  · rcases hu' with h3 | h3
    · exact Or.inr (h3.trans h2.symm)
    · exact Or.inl (h3.trans h1.symm)
  · exact absurd (h1.trans h2.symm) hne

theorem isPSL32_of_not_le
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h311 : Theorem311Stmt) (hRO : RankOneListedFacts.{0}) (h8 : Stmt3_3_8OneGroup)
    (hT : ¬ T ≤ Subgroup.normalizer (L : Set G)) : IsPSL 3 2 1 ↥(autOn L (vPlus L T)) := by
  obtain ⟨t, ht, htn, hMp, hcomm, hinf, hty⟩ := h8 G T M L D h hT
  rcases hty with ⟨n, hL⟩ | hP
  swap
  · exact hP
  exfalso
  set V := vPlus L T with hV
  have hHV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := (vPlus_reduced h.toSetup331).2.2.2.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hHV
  have htV : t ∈ Subgroup.normalizer (V : Set G) := hHV (Subgroup.mem_sup_right ht)
  have hLtV : CFSG.conjugate L t ≤ Subgroup.normalizer (V : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.normalizer (V : Set G)).mul_mem
      ((Subgroup.normalizer (V : Set G)).mul_mem (inv_mem htV) (hLV hx)) (inv_mem (inv_mem htV))
  set K₁ := autOn L V with hK₁
  set K₂ := autOn (CFSG.conjugate L t) V with hK₂
  have hn : 1 ≤ n := by
    rcases hL with ⟨-, ⟨-, hf, -⟩, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hf
    all_goals exact absurd h0 (by norm_num)
  have hR₁ : IsRankOneSylow ↥K₁ := hRO _ (isRankOneListed_of_lieModel hn hL)
  have hK₂eq : K₂ = K₁.map (MulAut.conj (conjAct V ⟨t⁻¹, inv_mem htV⟩)).toMonoidHom :=
    autOn_map_conj (X := L) (inv_mem htV)
  have hR₂ : IsRankOneSylow ↥K₂ := by
    rw [hK₂eq]
    exact hR₁.of_mulEquiv (K₁.equivMapOfInjective _ (MulAut.conj _).injective)
  obtain ⟨hKX, hXK, h2, hS⟩ := h.autOn_data
  have hKsup : autOn (mPlus L T) V = K₁ ⊔ K₂ := by
    rw [hMp]
    exact autOn_sup hLV hLtV
  have hLt : CFSG.conjugate L t = L.map (MulAut.conj t⁻¹).toMonoidHom := rfl
  have hcomp : ∀ a b : G, (L.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      L.map (MulAut.conj (a * b)).toMonoidHom := by
    intro a b
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hnotfix : ∀ a b : G, L.map (MulAut.conj a).toMonoidHom = L.map (MulAut.conj b).toMonoidHom →
      L.map (MulAut.conj (a⁻¹ * b)).toMonoidHom = L := by
    intro a b hab
    rw [← hcomp, ← hab, hcomp, inv_mul_cancel]
    ext x
    simp
  have hLne : L.map (MulAut.conj t⁻¹).toMonoidHom ≠ L := by
    intro heq
    apply htn
    have h1 : t⁻¹ ∈ Subgroup.normalizer (L : Set G) := Ch3Sec3.mem_normalizer_of_map_conj_eq heq
    simpa using inv_mem h1
  have hperm : ∀ s ∈ autOn T V, (K₁.map (MulAut.conj s).toMonoidHom = K₁ ∧
      K₂.map (MulAut.conj s).toMonoidHom = K₂) ∨
      (K₁.map (MulAut.conj s).toMonoidHom = K₂ ∧ K₂.map (MulAut.conj s).toMonoidHom = K₁) := by
    intro s hs
    obtain ⟨g, hgT, rfl⟩ := CFSG.QuasithinUnique.Setup.mem_autOn_iff.mp hs
    have hgH : (g : G) ∈ L ⊔ T := Subgroup.mem_sup_right hgT
    have e₁ : K₁.map (MulAut.conj (conjAct V g)).toMonoidHom =
        autOn (L.map (MulAut.conj (g : G)).toMonoidHom) V := (autOn_map_conj (X := L) g.2).symm
    have e₂ : K₂.map (MulAut.conj (conjAct V g)).toMonoidHom =
        autOn (L.map (MulAut.conj ((g : G) * t⁻¹)).toMonoidHom) V := by
      rw [← hcomp]
      exact (autOn_map_conj (X := CFSG.conjugate L t) g.2).symm
    rw [e₁, e₂]
    have hgt : (g : G) * t⁻¹ ∈ L ⊔ T :=
      (L ⊔ T).mul_mem hgH ((L ⊔ T).inv_mem (Subgroup.mem_sup_right ht))
    rcases h.map_conj_mem h38 hT ht htn hgH with h₁ | h₁ <;>
      rcases h.map_conj_mem h38 hT ht htn hgt with h₂ | h₂
    · exfalso
      apply hLne
      have := hnotfix _ _ (h₁.trans h₂.symm)
      rwa [show (g : G)⁻¹ * ((g : G) * t⁻¹) = t⁻¹ by group] at this
    · exact Or.inl ⟨by rw [h₁], by rw [h₂]⟩
    · exact Or.inr ⟨by rw [h₁], by rw [h₂]⟩
    · exfalso
      apply hLne
      have := hnotfix _ _ (h₁.trans h₂.symm)
      rwa [show (g : G)⁻¹ * ((g : G) * t⁻¹) = t⁻¹ by group] at this
  have hswap : ∃ s ∈ autOn T V, K₁.map (MulAut.conj s).toMonoidHom = K₂ :=
    ⟨conjAct V ⟨t⁻¹, inv_mem htV⟩,
      CFSG.QuasithinUnique.Setup.mem_autOn_iff.mpr ⟨⟨t⁻¹, inv_mem htV⟩, T.inv_mem ht, rfl⟩,
      hK₂eq.symm⟩
  obtain ⟨hSP, hne, hmax⟩ := le_normalizer_of_rankOne_prod hKX hXK h2 hS hKsup
    (fun a ha b hb => hcomm a ha b hb) hinf hR₁ hR₂ hperm hswap
  exact h.not_isUniqueMaxOver h38 h39 h311
    (exists_isUniqueMaxOver_of_autOn hHV le_sup_right
      (pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf) (h.centralizer_vPlus h38 h39).2.2
      inf_le_left hne (le_inf hS.1 hSP) fun Y hSY hYX hYne => hmax Y hSY hYX hYne)

end Hyp331

theorem stmt3_3_10_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h311 : Theorem311Stmt)
    (hRO : RankOneListedFacts.{0}) (h8 : Stmt3_3_8OneGroup) : Stmt3_3_10 := by
  intro G _ _ T M L D h
  exact ⟨fun H hH hu => h.pCoreOf_sup_ne_bot h311 hH hu,
    fun n => h.not_lieModel_psl2 h38 h39 h311 hRO n,
    fun hT => h.isPSL32_of_not_le h38 h39 h311 hRO h8 hT⟩

end CFSG.Quasithin.H13
