module

public import CFSG.Quasithin.EmptyFaithful.S152He7Nat
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag5
public import CFSG.Quasithin.Background.SmithB45LnL4Main
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

section Restr

variable {M : Type} [CommGroup M] [Finite M] (Λ : Subgroup (MulAut M)) (J : Subgroup M)
  (hJ : ∀ l ∈ Λ, ∀ v ∈ J, l v ∈ J)

@[expose] def resEquiv (l : ↥Λ) : MulAut ↥J where
  toFun v := ⟨(l : MulAut M) (v : M), hJ l l.2 v v.2⟩
  invFun v := ⟨(l : MulAut M)⁻¹ (v : M), hJ _ (Λ.inv_mem l.2) v v.2⟩
  left_inv v := Subtype.ext (MulAut.inv_apply_self M (l : MulAut M) (v : M))
  right_inv v := Subtype.ext (MulAut.apply_inv_self M (l : MulAut M) (v : M))
  map_mul' a b := Subtype.ext (map_mul (l : MulAut M) (a : M) (b : M))

@[expose] def resAut : ↥Λ →* MulAut ↥J where
  toFun := resEquiv Λ J hJ
  map_one' := MulEquiv.ext fun _ => rfl
  map_mul' _ _ := MulEquiv.ext fun _ => rfl

omit [Finite M] in
theorem resAut_apply (l : ↥Λ) (v : ↥J) :
    ((resAut Λ J hJ l v : ↥J) : M) = (l : MulAut M) (v : M) :=
  rfl

omit [Finite M] in
theorem resAut_injective (hs : IsSimpleGroup ↥Λ)
    (hnt : ∃ l ∈ Λ, ∃ v ∈ J, l v ≠ v) : Function.Injective (resAut Λ J hJ) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (resAut Λ J hJ).ker with h | h
  · exact h
  · exfalso
    obtain ⟨l, hl, v, hv, hlv⟩ := hnt
    have h1 : resAut Λ J hJ ⟨l, hl⟩ = 1 := by
      rw [← MonoidHom.mem_ker, h]
      exact Subgroup.mem_top _
    apply hlv
    have := congrArg (fun φ : MulAut ↥J => ((φ ⟨v, hv⟩ : ↥J) : M)) h1
    simpa [resAut_apply] using this

end Restr

variable {M : Type} [CommGroup M] [Finite M] {Λ : Subgroup (MulAut M)} {J : Subgroup M}

theorem classify_sub [Module (ZMod 2) (Additive ↥J)] (hA21 : AsA21SQTKSection) {X : Type}
    [Group X] [Finite X]
    (hX : SQTKGroup X) {Hs : Subgroup X} (σ : ↥Hs →* ↥Λ) (hσ : Function.Surjective σ)
    (e : ↥Λ ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)))
    (hJ : ∀ l ∈ Λ, ∀ v ∈ J, l v ∈ J)
    (hirr : ∀ J' : Subgroup M, J' ≤ J → (∀ l ∈ Λ, ∀ v ∈ J', l v ∈ J') → J' = ⊥ ∨ J' = J)
    (hnt : ∃ l ∈ Λ, ∃ v ∈ J, l v ≠ v) {E : Subgroup (MulAut M)} (hEΛ : E ≤ Λ) (hE1 : E ≠ ⊥)
    (hEab : IsElemAbelian2 E) (hEJ : (J ⊓ fixV E).relIndex J ≤ Nat.card E ^ 2) :
    (∃ κ : B42Ln.G4 ≃* B42Ln.G4, ∃ β : Additive ↥J ≃ₗ[ZMod 2] (Fin 4 → ZMod 2),
      ∀ (l : ↥Λ) (v : ↥J), β (Additive.ofMul ⟨(l : MulAut M) v, hJ l l.2 v v.2⟩) =
        B42Ln.natRep4 (κ (B42Ln.phiOf4 e l)) (β (Additive.ofMul v))) ∨
    (∃ β : Additive ↥J ≃ₗ[ZMod 2] (Fin 6 → ZMod 2),
      ∀ (l : ↥Λ) (v : ↥J), β (Additive.ofMul ⟨(l : MulAut M) v, hJ l l.2 v v.2⟩) =
        B42Ln.wedgeRep4' (B42Ln.phiOf4 e l) (β (Additive.ofMul v))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsl : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.sl_isSimple_of_card_two (Nat.card_zmod 2) (by norm_num)
  have hsΛ : IsSimpleGroup ↥Λ := (e.trans B42Ln.E4.symm).isSimpleGroup
  set ρ := resAut Λ J hJ with hρ
  have hρi : Function.Injective ρ := resAut_injective Λ J hJ hsΛ hnt
  set ΛJ : Subgroup (MulAut ↥J) := ρ.range with hΛJ
  let ι : ↥Λ ≃* ↥ΛJ := MonoidHom.ofInjective hρi
  have hι : ∀ l, ((ι l : ↥ΛJ) : MulAut ↥J) = ρ l := fun l => rfl
  set eJ : ↥ΛJ ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) := ι.symm.trans e with heJ
  have hphi : ∀ l : ↥Λ, B42Ln.phiOf4 eJ (ι l) = B42Ln.phiOf4 e l := by
    intro l
    simp [B42Ln.phiOf4, heJ]
  have hsJ : IsSimpleGroup ↥ΛJ := ι.symm.isSimpleGroup
  obtain ⟨a₀, b₀, hab₀⟩ :=
    CFSG.QuasithinUnique.Vol2Native.A312L.sl_nonabelian_of_card_two (Nat.card_zmod 2)
      (by norm_num : 3 ≤ 4)
  set φJ := B42Ln.phiOf4 eJ with hφJ
  have hncJ : ∃ a b : ↥ΛJ, a * b ≠ b * a :=
    ⟨φJ.symm a₀, φJ.symm b₀, fun h => hab₀ (by
      have := congrArg φJ h
      simpa using this)⟩
  have hcard : Nat.card ↥ΛJ = 20160 := by
    rw [Nat.card_congr φJ.toEquiv, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq
      (by norm_num), Nat.card_zmod]
    decide
  have hnot2 : ¬ IsPGroup 2 ↥ΛJ := by
    intro hp
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [hcard] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 20160)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hperf : Group.IsPerfect ↥ΛJ := He7.isPerfect_of_simple_noncomm hncJ
  have hqJ : CFSG.IsQuasisimple ↥ΛJ := LRed5.isQuasisimple_of_simple_nonabelian hperf hncJ
  have hSQ : SQTKGroup ↥ΛJ :=
    B69.sqtk_of_surj hA21 hX ((ι.toMonoidHom).comp σ) (ι.surjective.comp hσ) hqJ
  have hirrJ : ∀ U : Subgroup ↥J, (∀ l ∈ ΛJ, ∀ u ∈ U, l u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    have hU' : ∀ l ∈ Λ, ∀ v ∈ U.map J.subtype, l v ∈ U.map J.subtype := by
      rintro l hl _ ⟨u, hu, rfl⟩
      exact ⟨ρ ⟨l, hl⟩ u, hU _ ⟨⟨l, hl⟩, rfl⟩ u hu, rfl⟩
    rcases hirr _ (Subgroup.map_subtype_le U) hU' with h | h
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).mp h
    · right
      rw [eq_top_iff]
      intro u _
      have hu : (u : M) ∈ U.map J.subtype := by rw [h]; exact u.2
      obtain ⟨u', hu', huu⟩ := hu
      rw [show u = u' from Subtype.ext huu.symm]
      exact hu'
  have hntJ : (⊤ : Subgroup ↥J) ≠ ⊥ := by
    intro h
    obtain ⟨l, hl, v, hv, hlv⟩ := hnt
    have : (⟨v, hv⟩ : ↥J) = 1 := by
      have h1 : (⟨v, hv⟩ : ↥J) ∈ (⊤ : Subgroup ↥J) := trivial
      rwa [h, Subgroup.mem_bot] at h1
    have hv1 : v = 1 := congrArg Subtype.val this
    rw [hv1, map_one] at hlv
    exact hlv rfl
  have hb4 : B4Hyp ΛJ ΛJ := He7.b4Hyp_of_simple hsJ hncJ hnot2 hSQ hirrJ hntJ
  have hZ : Subgroup.center ↥ΛJ = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥ΛJ) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hncJ
      have ha : a ∈ Subgroup.center ↥ΛJ := by rw [h]; exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  set EJ : Subgroup (MulAut ↥J) := (E.subgroupOf Λ).map ρ with hEJdef
  have hEJΛ : EJ ≤ ΛJ := Subgroup.map_le_range _ _
  have hcardE : Nat.card EJ = Nat.card E := by
    rw [hEJdef, Subgroup.card_map_of_injective hρi,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEΛ).toEquiv]
  have hA : IsA2 ΛJ EJ := by
    refine ⟨hEJΛ, ?_, ?_, ?_⟩
    · intro h
      apply hE1
      rw [eq_bot_iff]
      intro x hx
      have h1 : ρ ⟨x, hEΛ hx⟩ ∈ EJ := ⟨⟨x, hEΛ hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
      rw [h, Subgroup.mem_bot, ← map_one ρ] at h1
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val (hρi h1))
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hEab.1 _ (Subgroup.mem_subgroupOf.mp hx) _
        (Subgroup.mem_subgroupOf.mp hy))
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have h2 : x ^ 2 = 1 := Subtype.ext (by
        simpa using hEab.2 _ (Subgroup.mem_subgroupOf.mp hx))
      rw [h2, map_one]
  have hfixJ : fixV EJ = (J ⊓ fixV E).subgroupOf J := by
    ext v
    rw [mem_fixV, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_fixV]
    constructor
    · intro h
      exact ⟨v.2, fun x hx =>
        congrArg Subtype.val (h _ ⟨⟨x, hEΛ hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩)⟩
    · rintro ⟨-, h⟩ _ ⟨x, hx, rfl⟩
      exact Subtype.ext (h x (Subgroup.mem_subgroupOf.mp hx))
  have h2F : (fixV EJ).index ≤ Nat.card EJ ^ 2 := by
    rw [hfixJ, hcardE, ← Subgroup.relIndex]
    exact hEJ
  have : Finite (Additive ↥J) := inferInstanceAs (Finite ↥J)
  have : Nontrivial ↥J := B42Ln.nontrivial_of_equiv4 eJ
  have hρs : SmithCurtis.IsSimpleRep (B42Ln.repOf4 φJ) :=
    B42Ln.isSimpleRep_repOf4 φJ (B42Ln.irr_of_isIrrSec hb4.2.2.2)
  have hmodel : B42Ln.L4Model (B42Ln.repOf4 φJ) := by
    rcases B45Ln.card_le_or_l4Model hb4 hZ eJ hA h2F with hV18 | hm
    · have hcard20 : ∀ β : Additive ↥J ≃ₗ[ZMod 2] (Fin 20 → ZMod 2), False := fun β => by
        have h1 : Nat.card ↥J = 2 ^ 20 := by
          rw [show Nat.card ↥J = Nat.card (Additive ↥J) from rfl, Nat.card_congr β.toEquiv,
            Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
          rfl
        omega
      rcases B45Ln.type_cases hρs with hm | h24 | ⟨β, -⟩ | ⟨β, -⟩ | ⟨β, hβ⟩
      · exact hm
      · exfalso
        have h1 : 2 ^ 24 ≤ Nat.card ↥J := by
          rw [B42Ln.card_eq_two_pow_finrank]
          exact Nat.pow_le_pow_right (by norm_num) h24
        omega
      · exact (hcard20 β).elim
      · exact (hcard20 β).elim
      · exact (B45Ln.false_of_rep14 hb4 hZ eJ hβ hA h2F).elim
    · exact hm
  have hrep : ∀ (l : ↥Λ) (v : ↥J), B42Ln.repOf4 φJ (B42Ln.phiOf4 e l) (Additive.ofMul v) =
      Additive.ofMul ⟨(l : MulAut M) v, hJ l l.2 v v.2⟩ := by
    intro l v
    rw [← hphi l, hφJ, B42Ln.repOf4_apply_iso]
    rfl
  rcases hmodel with htriv | ⟨κ, β, hβ⟩ | ⟨β, hβ⟩
  · exact (B42Ln.not_trivial4 eJ htriv).elim
  · refine Or.inl ⟨κ, β, fun l v => ?_⟩
    rw [← hrep l v, hβ]
  · refine Or.inr ⟨β, fun l v => ?_⟩
    rw [← hrep l v, hβ]

end CFSG.Quasithin.H13.L32A.C
