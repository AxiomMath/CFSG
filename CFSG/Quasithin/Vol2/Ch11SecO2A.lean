module

public import CFSG.Quasithin.Vol2.Ch11SecBK7I
public import CFSG.Quasithin.Vol2.Ch11G2Q8AutV
public import CFSG.Quasithin.Vol2.Ch11SecA12Out2
public import CFSG.Quasithin.Vol2.Ch11SecAKA2
public import CFSG.Quasithin.Vol2.Ch11SecO1B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Open (pCoreOf)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (Usp)
open scoped IsMulCommutative

namespace O2

variable {G : Type} [Group G]

theorem le_commutator_of_fix {V Y : Subgroup G} [IsMulCommutative ↥V] [Finite ↥V] {y : G}
    (hyY : y ∈ Y) (hy : y ∈ Subgroup.normalizer (V : Set G))
    (hfix : ∀ v : ↥V, SecA.conjV V y hy v = v → v = 1) : V ≤ ⁅V, Y⁆ := by
  let φ : ↥V →* ↥V :=
    { toFun := fun v => SecA.conjV V y hy v * v⁻¹
      map_one' := by rw [map_one, inv_one, mul_one]
      map_mul' := fun a b => by rw [map_mul, mul_inv, mul_mul_mul_comm] }
  have hφ : ∀ v, φ v = SecA.conjV V y hy v * v⁻¹ := fun v => rfl
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro v hv
    rw [MonoidHom.mem_ker, hφ, mul_inv_eq_one] at hv
    exact Subgroup.mem_bot.mpr (hfix v hv)
  intro w hw
  obtain ⟨v, hv⟩ := Finite.surjective_of_injective hinj ⟨w, hw⟩
  have h1 := SecB.K7.conjV_comm_mem hyY hy v
  rw [← hφ, hv] at h1
  exact h1

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem lOf_sup_le (hS : SecD.NatSetting11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) :
    LOf L V₁ ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) ⊓ Subgroup.normalizer (L : Set G) ⊓
      Subgroup.normalizer (V₁ : Set G) ⊓ Subgroup.normalizer (LOf L V₁ : Set G) := by
  have h : LOf L V₁ ≤ L ⊓ Subgroup.normalizer (V₁ : Set G) := perfectCore_le _
  have hT : T ≤ Subgroup.normalizer ((L ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) :
      Set G) :=
    (le_inf hS.normal (hV₁.2.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  refine sup_le (le_inf (le_inf (le_inf ?_ ?_) ?_) Subgroup.le_normalizer)
    (le_inf (le_inf (le_inf (SecA.T_le_normalizer_fsuV T I) hS.normal) hV₁.2)
      (hT.trans (normalizer_le_normalizer_perfectCore _)))
  · exact h.trans (inf_le_left.trans hS.le_normalizer)
  · exact h.trans (inf_le_left.trans Subgroup.le_normalizer)
  · exact h.trans inf_le_right

theorem r1_le (hS : SecD.NatSetting11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    ROf T L V₁ ≤ Subgroup.normalizer (fsuV T I : Set G) ⊓ Subgroup.normalizer (L : Set G) ⊓
      Subgroup.normalizer (V₁ : Set G) ⊓ Subgroup.normalizer (LOf L V₁ : Set G) :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (lOf_sup_le hS hV₁)

theorem l1_le_normalizer (hS : SecD.NatSetting11 G T L I n) (V₁ : Subgroup G) :
    LOf L V₁ ≤ Subgroup.normalizer (fsuV T I : Set G) :=
  (perfectCore_le _).trans (inf_le_left.trans hS.le_normalizer)

theorem comm_mem_pCoreOf (hS : SecD.NatSetting11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) {r l : G} (hr : r ∈ ROf T L V₁) (hl : l ∈ LOf L V₁) :
    r * l * r⁻¹ * l⁻¹ ∈ pCoreOf 2 (LOf L V₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := ROf T L V₁ with hR
  have hNR : LOf L V₁ ⊔ T ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hle : R ⊓ LOf L V₁ ≤ pCoreOf 2 (LOf L V₁) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
    exact (le_inf (le_sup_left.trans hNR) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  refine hle ⟨?_, ?_⟩
  · have h1 : l * r⁻¹ * l⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (hNR (le_sup_left (α := Subgroup G) hl)) _).mp
        (R.inv_mem hr)
    have := R.mul_mem hr h1
    rwa [← mul_assoc, ← mul_assoc] at this
  · have h1 : r * l * r⁻¹ ∈ LOf L V₁ :=
      (Subgroup.mem_normalizer_iff.mp (r1_le hS hV₁ hr).2 _).mp hl
    exact (LOf L V₁).mul_mem h1 ((LOf L V₁).inv_mem hl)

theorem pCoreOf_p1_eq (hS : SecD.NatSetting11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) :
    pCoreOf 2 (perfectCore (autOn L (fsuV T I) ⊓ SecA.stabW (V₁.subgroupOf (fsuV T I)))) =
      autOn (pCoreOf 2 (LOf L V₁)) (fsuV T I) := by
  have hC₁ : IsPGroup 2 ↥(LOf L V₁ ⊓ Subgroup.centralizer (fsuV T I : Set G)) :=
    (SecO1.isPGroup_inf_centralizer hS).to_le
      (inf_le_inf_right _ ((perfectCore_le _).trans inf_le_left))
  rw [← SecA.autOn_lOf hS.le_normalizer (SecA.IsVi.le_fsuV hV₁),
    SecA.autOn_pCoreOf (l1_le_normalizer hS V₁) hC₁]

theorem exists_coord (hS : SecD.NatSetting11 G T L I n) (hk : KindSp4 L (fsuV T I) n)
    [IsMulCommutative ↥(fsuV T I)] :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      ∃ (π : ↥(StatedSp 2 K) →* ↥(autOn L (fsuV T I))) (f : ↥(fsuV T I) → (Fin 2 ⊕ Fin 2 → K))
        (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f)
        (g : StatedSp 2 K),
        (FFModel.nat (StatedSp 2 K)).RealizesVia (autOn L (fsuV T I)) ⊤ ⊥ π ∧
        (∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
          ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I))) ∧
        (∀ U : Subgroup G, IsVi T L I n 1 U →
          U.subgroupOf (fsuV T I) = hf.pre (gmapSp g (spLine K)).toAddSubgroup) ∧
        (∀ U : Subgroup G, IsVi T L I n 2 U →
          U.subgroupOf (fsuV T I) = hf.pre (gmapSp g (spPlane K)).toAddSubgroup) ∧
        (∀ U : Subgroup G, IsVi T L I n 3 U →
          U.subgroupOf (fsuV T I) = hf.pre (gmapSp g (spHyp K)).toAddSubgroup) := by
  have hn : 2 ≤ n := hS.one_lt
  obtain ⟨K, _, _, hK, π, f, hπ, hf⟩ := SecO1.exists_coord_sp4 hS hk
  have : CharP K 2 := charP_two_of_card (by omega) hK
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK (by omega) hf (SecO1.isSylowTwoOf_P hS)
  have hpre : ∀ {i : ℕ} {U : Subgroup G}, IsVi T L I n i U →
      ∃ S : Submodule K (Fin 2 ⊕ Fin 2 → K), UStableSp S ∧ Nat.card S = Nat.card K ^ i ∧
        U.subgroupOf (fsuV T I) = hf.pre (gmapSp g S).toAddSubgroup := fun hU =>
    exists_eq_pre_of_isFlagW_sp (SecO1.sq_eq_one hS) hf hg
      (by rw [hK]; exact SecO1.isFlagW_of_isVi hS hU)
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK, π, f, hf, g, hπ, hg,
    fun U hU => ?_, fun U hU => ?_, fun U hU => ?_⟩
  · obtain ⟨S, hS', hc, hU'⟩ := hpre hU
    rw [hU', (eq_std_of_stable_sp hS').1 (by rw [hc, pow_one])]
  · obtain ⟨S, hS', hc, hU'⟩ := hpre hU
    rw [hU', (eq_std_of_stable_sp hS').2.1 hc]
  · obtain ⟨S, hS', hc, hU'⟩ := hpre hU
    rw [hU', (eq_std_of_stable_sp hS').2.2 hc]

section Coord

variable [IsMulCommutative ↥(fsuV T I)] {K : Type} [Field K] [Finite K] [CharP K 2]
  {π : ↥(StatedSp 2 K) →* ↥(autOn L (fsuV T I))} {f : ↥(fsuV T I) → (Fin 2 ⊕ Fin 2 → K)}

omit [Finite G] [Finite K] [CharP K 2] in
theorem mem_iff_of_eq {hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f}
    {g : StatedSp 2 K} {S : Submodule K (Fin 2 ⊕ Fin 2 → K)} {U : Subgroup G}
    (hU : U.subgroupOf (fsuV T I) = hf.pre (gmapSp g S).toAddSubgroup) (v : ↥(fsuV T I)) :
    (v : G) ∈ U ↔ mat 2 K g⁻¹ *ᵥ f v ∈ S := by
  rw [← Subgroup.mem_subgroupOf, hU, hf.mem_pre, Submodule.mem_toAddSubgroup, mem_gmapSp]

omit [Finite G] [Finite K] in
theorem mem_v3_iff {hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f}
    {g : StatedSp 2 K} {V₃ : Subgroup G}
    (hV₃ : V₃.subgroupOf (fsuV T I) = hf.pre (gmapSp g (spHyp K)).toAddSubgroup)
    (v : ↥(fsuV T I)) :
    (v : G) ∈ V₃ ↔ Matrix.toBilin' (spJ K) (f v) (mat 2 K g *ᵥ vec4 1 0 0 0) = 0 := by
  rw [← Subgroup.mem_subgroupOf, hV₃, hf.mem_pre, Submodule.mem_toAddSubgroup, mem_gS3_iff,
    SecB.K7.bil_comm]

omit [Finite G] [Finite K] [CharP K 2] in
theorem mem_v1_iff {hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f}
    {g : StatedSp 2 K} {V₁ : Subgroup G}
    (hV₁ : V₁.subgroupOf (fsuV T I) = hf.pre (gmapSp g (spLine K)).toAddSubgroup)
    (v : ↥(fsuV T I)) :
    (v : G) ∈ V₁ ↔ ∃ c : K, f v = c • (mat 2 K g *ᵥ vec4 1 0 0 0) := by
  rw [← Subgroup.mem_subgroupOf, hV₁, hf.mem_pre, Submodule.mem_toAddSubgroup, mem_gS1_iff]

theorem exists_core_r1 (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hπ : (FFModel.nat (StatedSp 2 K)).RealizesVia (autOn L (fsuV T I)) ⊤ ⊥ π)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f) {g : StatedSp 2 K}
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hV₁g : V₁.subgroupOf (fsuV T I) = hf.pre (gmapSp g (spLine K)).toAddSubgroup)
    {r : G} (hr : r ∈ ROf T L V₁) :
    ∃ N ∈ pCoreOf 2 (perfectCore (Q2 K 0)),
      SecA.conjV (fsuV T I) r (r1_le hS hV₁ hr).1.1.1 = psiSp π g N := by
  have hn : 2 ≤ n := hS.one_lt
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  have hW := SecO1.sq_eq_one hS
  have hP := SecO1.isSylowTwoOf_P hS
  have hU := SecO1.isFlagW_of_isVi hS hV₁
  have hfix := factRadicalFixedSp4_holds K n hn hK _ hW _ ⊥ π hπ _ hP _ hU
  have hpt := factPointSp4_holds K n hn hK _ hW _ ⊥ π hπ _ hP _ hU
  obtain ⟨⟨⟨hrV, hrL⟩, -⟩, -⟩ := r1_le hS hV₁ hr
  have hτ2 : ∃ k : ℕ, SecA.conjV (fsuV T I) r hrV ^ 2 ^ k = 1 := by
    obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _ ⟨r, hr⟩
    exact ⟨m, SecA.conjV_pow_eq_one _ hrV (by simpa using congrArg Subtype.val hm)⟩
  have hτH : ∀ h ∈ autOn L (fsuV T I), SecA.conjV (fsuV T I) r hrV * h *
      (SecA.conjV (fsuV T I) r hrV)⁻¹ ∈ autOn L (fsuV T I) := fun h hh =>
    G2Q8.conjV_mul_conjV_inv_mem hrL hrV hh
  have hP₁ : perfectCore (autOn L (fsuV T I) ⊓ SecA.stabW (V₁.subgroupOf (fsuV T I))) =
      autOn (LOf L V₁) (fsuV T I) :=
    (SecA.autOn_lOf hS.le_normalizer (SecA.IsVi.le_fsuV hV₁)).symm
  have hO := pCoreOf_p1_eq hS hV₁
  have hτc : ∀ x : ↥(perfectCore (autOn L (fsuV T I) ⊓ SecA.stabW
      (V₁.subgroupOf (fsuV T I)))), ∃ y : ↥(perfectCore (autOn L (fsuV T I) ⊓ SecA.stabW
        (V₁.subgroupOf (fsuV T I)))), y ∈ CFSG.pCore 2 ↥(perfectCore (autOn L (fsuV T I) ⊓
          SecA.stabW (V₁.subgroupOf (fsuV T I)))) ∧
        SecA.conjV (fsuV T I) r hrV * (x : MulAut ↥(fsuV T I)) *
          (SecA.conjV (fsuV T I) r hrV)⁻¹ = (y : MulAut ↥(fsuV T I)) * x := by
    intro x
    have hx : (x : MulAut ↥(fsuV T I)) ∈ autOn (LOf L V₁) (fsuV T I) := by
      rw [← hP₁]
      exact x.2
    obtain ⟨l, hl, hlV, hxl⟩ := SecA.mem_autOn_iff.mp hx
    have hcV : r * l * r⁻¹ * l⁻¹ ∈ Subgroup.normalizer (fsuV T I : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrV hlV)
        (Subgroup.inv_mem _ hrV)) (Subgroup.inv_mem _ hlV)
    have hmem : SecA.conjV (fsuV T I) r hrV * (x : MulAut ↥(fsuV T I)) *
        (SecA.conjV (fsuV T I) r hrV)⁻¹ * (x : MulAut ↥(fsuV T I))⁻¹ ∈
          pCoreOf 2 (perfectCore (autOn L (fsuV T I) ⊓ SecA.stabW
            (V₁.subgroupOf (fsuV T I)))) := by
      rw [hO, hxl, ← SecA.conjV_inv, ← SecA.conjV_inv, ← SecA.conjV_mul, ← SecA.conjV_mul,
        ← SecA.conjV_mul]
      exact SecA.conjV_mem_autOn (comm_mem_pCoreOf hS hV₁ hr hl) hcV
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
    refine ⟨y, by exact hy, ?_⟩
    have hyx' : (y : MulAut ↥(fsuV T I)) = SecA.conjV (fsuV T I) r hrV *
        (x : MulAut ↥(fsuV T I)) * (SecA.conjV (fsuV T I) r hrV)⁻¹ *
          (x : MulAut ↥(fsuV T I))⁻¹ := hyx
    rw [hyx', inv_mul_cancel_right]
  obtain ⟨N, hN, hact⟩ := KA.exists_core hK4 hf g hV₁g hfix hpt hτ2
    (SecO1.mem_stabW_bot _) hτH hτc
  exact ⟨N, hN, MulEquiv.ext fun w => SecO1.IsCoord.injective_of_bot hf (hact w)⟩

omit [CharP K 2] in
theorem exists_act_l1 (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hπ : (FFModel.nat (StatedSp 2 K)).RealizesVia (autOn L (fsuV T I)) ⊤ ⊥ π)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f) {g : StatedSp 2 K}
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hV₁g : V₁.subgroupOf (fsuV T I) = hf.pre (gmapSp g (spLine K)).toAddSubgroup)
    {l : G} (hl : l ∈ LOf L V₁) :
    ∃ δ : ↥(StatedSp 2 K), SecA.conjV (fsuV T I) l (l1_le_normalizer hS V₁ hl) =
        ((π δ : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) ∧
      mat 2 K δ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0) = mat 2 K g *ᵥ vec4 1 0 0 0 := by
  have hn : 2 ≤ n := hS.one_lt
  have hpt := factPointSp4_holds K n hn hK _ (SecO1.sq_eq_one hS) _ ⊥ π hπ _
    (SecO1.isSylowTwoOf_P hS) _ (SecO1.isFlagW_of_isVi hS hV₁)
  have hP₁ : SecA.conjV (fsuV T I) l (l1_le_normalizer hS V₁ hl) ∈
      perfectCore (autOn L (fsuV T I) ⊓ SecA.stabW (V₁.subgroupOf (fsuV T I))) := by
    rw [← SecA.autOn_lOf hS.le_normalizer (SecA.IsVi.le_fsuV hV₁)]
    exact SecA.conjV_mem_autOn hl _
  obtain ⟨δ, hδ⟩ : ∃ δ : ↥(StatedSp 2 K), π δ = ⟨_, (perfectCore_le _ hP₁).1⟩ :=
    hf.onto ⟨_, (perfectCore_le _ hP₁).1⟩
  have hδ' : SecA.conjV (fsuV T I) l (l1_le_normalizer hS V₁ hl) =
      ((π δ : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) := by rw [hδ]
  refine ⟨δ, hδ', ?_⟩
  obtain ⟨u₀, hu₀⟩ := hf.surj (mat 2 K g *ᵥ vec4 1 0 0 0)
  have hu₀U : u₀ ∈ V₁.subgroupOf (fsuV T I) := by
    rw [hV₁g, hf.mem_pre, Submodule.mem_toAddSubgroup, mem_gS1_iff]
    exact ⟨1, by rw [hu₀, one_smul]⟩
  have h1 := hpt _ hP₁ u₀ hu₀U
  rw [Subgroup.mem_bot, mul_inv_eq_one, hδ'] at h1
  have h2 := congrArg f h1
  rw [hf.act4, hu₀] at h2
  exact h2

theorem exists_trv_of_r1 (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hπ : (FFModel.nat (StatedSp 2 K)).RealizesVia (autOn L (fsuV T I)) ⊤ ⊥ π)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f) {g : StatedSp 2 K}
    {V₁ V₃ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hV₁g : V₁.subgroupOf (fsuV T I) = hf.pre (gmapSp g (spLine K)).toAddSubgroup)
    (hV₃g : V₃.subgroupOf (fsuV T I) = hf.pre (gmapSp g (spHyp K)).toAddSubgroup)
    {r : G} (hr : r ∈ ROf T L V₁) (hrV₃ : ∀ u ∈ V₃, r * u = u * r) :
    ∃ c : K, SecA.conjV (fsuV T I) r (r1_le hS hV₁ hr).1.1.1 =
      ((π (SecB.K7.trv (mat 2 K g *ᵥ vec4 1 0 0 0) c) : ↥(autOn L (fsuV T I))) :
        MulAut ↥(fsuV T I)) := by
  obtain ⟨N, -, hN⟩ := exists_core_r1 hS hK hπ hf hV₁ hV₁g hr
  obtain ⟨c, hc⟩ := SecB.K7.eq_trv_of_fix (γ := g * N * g⁻¹) (v0_ne_zero g) fun x hx => by
    obtain ⟨u, rfl⟩ := hf.surj x
    have hu : (u : G) ∈ V₃ := (mem_v3_iff hV₃g u).mpr hx
    have h1 : SecA.conjV (fsuV T I) r (r1_le hS hV₁ hr).1.1.1 u = u :=
      Subtype.ext (by rw [SecA.conjV_apply_coe, hrV₃ u hu, mul_inv_cancel_right])
    rw [hN, psiSp_apply] at h1
    have h2 := congrArg f h1
    rwa [hf.act4] at h2
  exact ⟨c, by rw [hN, psiSp_apply, hc]⟩

end Coord

end O2

end CFSG.Quasithin.Vol2.Ch11.SecF
