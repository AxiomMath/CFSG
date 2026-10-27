module

public import CFSG.Quasithin.MS93.Burnside.Mag568A
public import CFSG.Quasithin.MS93.Burnside.Mag568LA

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S34F
open scoped commutatorElement Matrix

section Group

variable {Γ : Type} [Group Γ]

theorem burnsideMag568_commutator_mem_of_mem {X : Subgroup Γ} {v a : Γ} (hv : v ∈ X)
    (ha : a ∈ Subgroup.normalizer (X : Set Γ)) : ⁅v, a⁆ ∈ X := by
  rw [commutatorElement_def]
  have h1 : a * v⁻¹ * a⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp ha _).mp (X.inv_mem hv)
  have e : v * a * v⁻¹ * a⁻¹ = v * (a * v⁻¹ * a⁻¹) := by group
  rw [e]
  exact X.mul_mem hv h1

end Group

section Dict

variable {G : Type} [Group G] {K V : Subgroup G} {F : Type} [Field F]
  {φ : ↥K →* ↥(StatedSL 3 F)}

theorem burnsideMag568_mem_commutator_iff (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1)
    {A : Subgroup G} (hA : A ≤ K) (v : ↥V) :
    (v : G) ∈ ⁅V, A⁆ ↔ natVec h v ∈ commN (natImage φ A) := by
  have hVA : ⁅V, A⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp (hA.trans h.1)
  constructor
  · intro hv
    have hp : ∀ y ∈ ⁅V, A⁆, ∃ hy : y ∈ V, natVec h ⟨y, hy⟩ ∈ commN (natImage φ A) := by
      intro y hy
      rw [Subgroup.commutator_def] at hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨v, hv, a, ha, rfl⟩ := hy
        have hmem : ⁅v, a⁆ ∈ V := hVA (Subgroup.commutator_mem_commutator hv ha)
        refine ⟨hmem, ?_⟩
        rw [natVec_commutator h ⟨a, hA ha⟩ ⟨v, hv⟩ ⟨_, hmem⟩ rfl]
        have hg : toSL3 φ ⟨a, hA ha⟩ ∈ natImage φ A := mem_natImage.mpr ⟨_, ha, rfl⟩
        have := sub_mem_commN hg (natVec h ⟨v, hv⟩)
        rw [← neg_sub]
        exact Submodule.neg_mem _ this
      | one =>
        refine ⟨V.one_mem, ?_⟩
        rw [show (⟨1, V.one_mem⟩ : ↥V) = 1 from rfl, natVec_one]
        exact Submodule.zero_mem _
      | mul a b _ _ iha ihb =>
        obtain ⟨ha, ha'⟩ := iha
        obtain ⟨hb, hb'⟩ := ihb
        refine ⟨V.mul_mem ha hb, ?_⟩
        rw [show (⟨a * b, V.mul_mem ha hb⟩ : ↥V) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, natVec_mul]
        exact Submodule.add_mem _ ha' hb'
      | inv a _ iha =>
        obtain ⟨ha, ha'⟩ := iha
        refine ⟨V.inv_mem ha, ?_⟩
        rw [show (⟨a⁻¹, V.inv_mem ha⟩ : ↥V) = (⟨a, ha⟩ : ↥V)⁻¹ from rfl, natVec_inv]
        exact Submodule.neg_mem _ ha'
    obtain ⟨_, hv'⟩ := hp v hv
    exact hv'
  · intro hv
    have hcl : natVec h v ∈ (commN (natImage φ A)).toAddSubgroup := hv
    rw [commN_eq_closure] at hcl
    have hp : ∀ x ∈ AddSubgroup.closure {y | ∃ g ∈ natImage φ A, ∃ x : Fin 3 → F,
        ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x = y},
        ∀ w : ↥V, natVec h w = x → (w : G) ∈ ⁅V, A⁆ := by
      intro x hx
      induction hx using AddSubgroup.closure_induction with
      | mem y hy =>
        intro w hw
        obtain ⟨g, hg, x, rfl⟩ := hy
        obtain ⟨a, haA, rfl⟩ := mem_natImage.mp hg
        obtain ⟨u, rfl⟩ := natVec_surjective h x
        have hmem : ⁅(u : G), (a : G)⁆ ∈ V := hVA (Subgroup.commutator_mem_commutator u.2 haA)
        have hc := natVec_commutator h a u ⟨_, hmem⟩ rfl
        have hw' : w = (⟨_, hmem⟩ : ↥V)⁻¹ := by
          apply natVec_injective h
          rw [hw, natVec_inv, hc, neg_sub]
        rw [hw']
        exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator u.2 haA)
      | zero =>
        intro w hw
        have : w = 1 := natVec_injective h (by rw [hw, natVec_one])
        rw [this]
        exact Subgroup.one_mem _
      | add x y _ _ ihx ihy =>
        intro w hw
        obtain ⟨u, hu⟩ := natVec_surjective h x
        obtain ⟨u', hu'⟩ := natVec_surjective h y
        have : w = u * u' := natVec_injective h (by rw [hw, natVec_mul, hu, hu'])
        rw [this]
        exact Subgroup.mul_mem _ (ihx u hu) (ihy u' hu')
      | neg x _ ihx =>
        intro w hw
        obtain ⟨u, hu⟩ := natVec_surjective h x
        have : w = u⁻¹ := natVec_injective h (by rw [hw, natVec_inv, hu])
        rw [this]
        exact Subgroup.inv_mem _ (ihx u hu)
    exact hp _ hcl v rfl

theorem burnsideMag568_mem_centralizer_iff (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1)
    {A : Subgroup G} (hA : A ≤ K) (v : ↥V) :
    (v : G) ∈ Subgroup.centralizer (A : Set G) ↔ natVec h v ∈ fixN (natImage φ A) := by
  rw [Subgroup.mem_centralizer_iff, mem_fixN]
  constructor
  · intro hv g hg
    obtain ⟨a, haA, rfl⟩ := mem_natImage.mp hg
    exact (commute_iff_natVec h a v).mp (hv _ haA)
  · intro hv a haA
    have := hv _ (mem_natImage.mpr ⟨⟨a, hA haA⟩, haA, rfl⟩)
    exact (commute_iff_natVec h ⟨a, hA haA⟩ v).mpr this

theorem burnsideMag568_natVec_commutator_of_normalizer
    (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) {x : G} (v u w : ↥V)
    (hu : (u : G) = x * v * x⁻¹) (hw : (w : G) = ⁅(v : G), x⁆) :
    natVec h w = natVec h v - natVec h u := by
  have hw' : w = v * u⁻¹ := by
    apply Subtype.ext
    rw [hw, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, hu]
    group
  rw [hw', natVec_mul, natVec_inv, sub_eq_add_neg]

theorem burnsideMag568_finrank_fixN_eq_one [Finite F]
    (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) {E : Subgroup G} (hE : E ≤ K)
    (hcard : Nat.card ↥(V ⊓ Subgroup.centralizer (E : Set G)) ^ 3 = Nat.card ↥V) :
    Module.finrank F (fixN (natImage φ E)) = 1 := by
  rw [card_inf_centralizer_eq h hE, card_fixN, card_eq_of_natural h, ← pow_mul] at hcard
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have := Nat.pow_right_injective hq hcard
  omega

theorem burnsideMag568_card_cube_of_finrank [Finite F]
    (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1) {E : Subgroup G} (hE : E ≤ K)
    (hf : Module.finrank F (fixN (natImage φ E)) = 1) :
    Nat.card ↥(V ⊓ Subgroup.centralizer (E : Set G)) ^ 3 = Nat.card ↥V := by
  rw [card_inf_centralizer_eq h hE, card_fixN, card_eq_of_natural h, hf, pow_one]

theorem burnsideMag568_le_of_orbit [Finite F] (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1)
    {A X : Subgroup G} (hA : A ≤ K) (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hXV : X ≤ V)
    (hf : Module.finrank F (fixN (natImage φ A)) = 2)
    (hcard : Nat.card ↥(natImage φ A) = Nat.card ↥(commN (natImage φ A)))
    {v : G} (hvX : v ∈ X) (hvC : v ∉ Subgroup.centralizer (A : Set G)) : ⁅V, A⁆ ≤ X := by
  have hVA : ⁅V, A⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp (hA.trans h.1)
  intro r hr
  set v' : ↥V := ⟨v, hXV hvX⟩
  set r' : ↥V := ⟨r, hVA hr⟩
  have hrc : natVec h r' ∈ commN (natImage φ A) :=
    (burnsideMag568_mem_commutator_iff h hA r').mp hr
  have hvf : natVec h v' ∉ fixN (natImage φ A) := fun hv =>
    hvC ((burnsideMag568_mem_centralizer_iff h hA v').mpr hv)
  obtain ⟨g, hg, hgv⟩ := burnsideMag568_exists_mulVec_sub_eq hf hcard hvf
    (Submodule.neg_mem _ hrc)
  obtain ⟨a, haA, rfl⟩ := mem_natImage.mp hg
  have hmem : ⁅(v : G), (a : G)⁆ ∈ V :=
    hVA (Subgroup.commutator_mem_commutator (hXV hvX) haA)
  have hc := natVec_commutator h a v' ⟨_, hmem⟩ rfl
  have heq : (⟨_, hmem⟩ : ↥V) = r' := by
    apply natVec_injective h
    rw [hc, ← neg_sub, hgv, neg_neg]
  have hr'' : r = ⁅(v : G), (a : G)⁆ := (congrArg Subtype.val heq).symm
  rw [hr'']
  exact burnsideMag568_commutator_mem_of_mem hvX (hAX haA)

theorem burnsideMag568_sup_eq_of_ne {A B W : Submodule F (Fin 3 → F)}
    (hA : Module.finrank F A = 1) (hB : Module.finrank F B = 1) (hW : Module.finrank F W = 2)
    (hAW : A ≤ W) (hBW : B ≤ W) (hne : A ≠ B) : A ⊔ B = W := by
  have hBA : ¬ B ≤ A := fun hle => hne (Submodule.eq_of_le_of_finrank_eq hle (by rw [hA, hB])).symm
  have hlt : A < A ⊔ B := lt_of_le_of_ne le_sup_left fun he => hBA (he ▸ le_sup_right)
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : Module.finrank F ↥(A ⊔ B) ≤ 2 := hW ▸ Submodule.finrank_mono (sup_le hAW hBW)
  exact Submodule.eq_of_le_of_finrank_eq (sup_le hAW hBW) (by rw [hW]; omega)

theorem burnsideMag568_mem_sup_of_natVec (h : IsSumOfNaturalModulesVia K V ⊥ φ false 1)
    {A B : Subgroup G} (hA : A ≤ K) (hB : B ≤ K) (w : ↥V)
    (hw : natVec h w ∈ commN (natImage φ A) ⊔ commN (natImage φ B)) :
    (w : G) ∈ ⁅V, A⁆ ⊔ ⁅V, B⁆ := by
  obtain ⟨y₁, hy₁, y₂, hy₂, hsum⟩ := Submodule.mem_sup.mp hw
  obtain ⟨u₁, rfl⟩ := natVec_surjective h y₁
  obtain ⟨u₂, rfl⟩ := natVec_surjective h y₂
  have hw' : w = u₁ * u₂ := natVec_injective h (by rw [natVec_mul, hsum])
  rw [hw', Subgroup.coe_mul]
  exact Subgroup.mul_mem_sup ((burnsideMag568_mem_commutator_iff h hA u₁).mpr hy₁)
    ((burnsideMag568_mem_commutator_iff h hB u₂).mpr hy₂)

end Dict

section Amalgam

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideMag568_isLine (h : PUHyp M T L) (hU : IsSL3U M T L) {δ : Vtx (puAmalgam h.le)}
    (hδ : IsMVtx _ δ) {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ S34F.flat h δ)
    (hcard : Nat.card ↥(Uloc h.le L δ ⊓ Subgroup.centralizer (E : Set _)) ^ 3 =
      Nat.card ↥(Uloc h.le L δ)) :
    mag568_IsLine h δ (Uloc h.le L δ ⊓ Subgroup.centralizer (E : Set _)) := by
  obtain ⟨n, F, _, _, φ, hcardF, hφs, hnat⟩ := exists_natural_flat h hU
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcardF]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  obtain ⟨ψ, -, hψ⟩ := exists_natural_flat_at h hφs hnat hδ
  have hℓ := burnsideMag568_finrank_fixN_eq_one hψ hE hcard
  refine ⟨inf_le_left, fun x hxf hxN hx2 => ?_⟩
  set a : ↥(S34F.flat h δ) := ⟨x, hxf⟩ with ha
  obtain ⟨k, hk⟩ := hx2 ⟨x, Subgroup.mem_zpowers x⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hgk : toSL3 ψ a ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : a ^ 2 ^ k = 1 := Subtype.ext (by simpa [ha] using hk')
    rw [this, map_one]
  have hstab : ∀ y ∈ fixN (natImage ψ E),
      ((toSL3 ψ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y ∈ fixN (natImage ψ E) := by
    intro y hy
    obtain ⟨v, rfl⟩ := natVec_surjective hψ y
    have hvC := (burnsideMag568_mem_centralizer_iff hψ hE v).mpr hy
    have hvZ : (v : (puAmalgam h.le).Universal) ∈
        Uloc h.le L δ ⊓ Subgroup.centralizer (E : Set _) := ⟨v.2, hvC⟩
    have hxv := (Subgroup.mem_normalizer_iff.mp hxN v).mp hvZ
    have h1 := natVec_conj hψ a v ⟨_, hxv.1⟩ rfl
    rw [← h1]
    exact (burnsideMag568_mem_centralizer_iff hψ hE _).mp hxv.2
  have hfix := burnsideMag568_fix_of_line hℓ hgk hstab
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzf : natVec hψ ⟨z, hz.1⟩ ∈ fixN (natImage ψ E) :=
    (burnsideMag568_mem_centralizer_iff hψ hE ⟨z, hz.1⟩).mp hz.2
  exact ((commute_iff_natVec hψ a ⟨z, hz.1⟩).mpr (hfix _ hzf)).symm

theorem burnsideMag568_rootGroup (h : PUHyp M T L) (hU : IsSL3U M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) {φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSL 3 F)}
    (hφs : Function.Surjective φ)
    (hnat : IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L) ⊥ φ false 1)
    {α μ : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α μ)
    (hbad : ¬ ⁅centerOf (burnsideSL3G_vb (puAmalgam h.le) μ), Ltil h.le L μ⁆ ≤ ZM _ μ)
    {ψ : ↥(S34F.flat h α) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (S34F.flat h α) (Uloc h.le L α) ⊥ ψ false 1) :
    Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) μ))) = 2 ∧
      Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) μ))) = 1 ∧
      Nat.card ↥(natImage ψ (ZM (puAmalgam h.le) μ)) = Nat.card F := by
  have hC := h.centHyp
  have hb0 := h.critDist_pos
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcard]
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hc' := ms22_iii _ h.hyp20 hb0 hC hc
  obtain ⟨ψμ, -, hψμ⟩ := exists_natural_flat_at h hφs hnat hc'.1
  obtain ⟨hf, hcardE, hrel, hR, hwf, -⟩ := s35_core_flat h hU hC hcard hc' hψμ hψ
  have hII : (Qv (puAmalgam h.le) α).relIndex (ZM (puAmalgam h.le) μ) =
      Nat.card ↥(critR (puAmalgam h.le) μ α) := by
    by_contra hne
    exact hbad (burnsideSL3G_centerOf_ltil_le_of_ne h hU hb hc' hne)
  set f := Module.finrank F (fixN (natImage ψμ (ZM (puAmalgam h.le) α))) with hfdef
  set w := Module.finrank F (commN (natImage ψμ (ZM (puAmalgam h.le) α))) with hwdef
  have h3 : 3 - f = w := by
    have : Nat.card F ^ (3 - f) = Nat.card F ^ w := by rw [← hrel, hII, hR]
    exact Nat.pow_right_injective hq this
  have hf3 : 3 - f ≠ 0 := by
    intro h0
    apply hc'.2.2
    rw [← Subgroup.relIndex_eq_one, hrel, h0, pow_zero]
  have hf2 : f = 2 := by omega
  have hw1 : w = 1 := by omega
  refine ⟨by rw [hf, hf2], ?_, by rw [hcardE, hrel, hf2]; simp⟩
  have hZK : ZM (puAmalgam h.le) μ ≤ S34F.flat h α := zm_le_flat h hU hc'
  have h1 := card_commutator_eq hψ hZK
  rw [← critR_eq_commutator_uloc h hC hc] at h1
  have h2 : Nat.card ↥(critR (puAmalgam h.le) α μ) = Nat.card F := by
    rw [critR, Subgroup.commutator_comm, ← critR, hR, hw1, pow_one]
  have h3' : Nat.card ↥(commN (natImage ψ (ZM (puAmalgam h.le) μ))) =
      Nat.card F ^ Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) μ))) :=
    Module.natCard_eq_pow_finrank
  rw [h2, h3'] at h1
  exact Nat.pow_right_injective hq (h1.symm.trans (pow_one _).symm)

end Amalgam

end CFSG.Quasithin.MS93.S4L
