module

public import CFSG.Quasithin.H13.QRCBenderModels
public import CFSG.Quasithin.H13.QRCPairLift
public import CFSG.Quasithin.Vol2.Ch3E213MP4C3

public section

namespace CFSG.Quasithin.Ch3E213M.P4C

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergBS CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup CFSG.Quasithin.H13.QRC
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.UnitaryModel CFSG.ShultStronglyClosedTI.TwoCoreGrowth

theorem normalizer_root_eq {k : Type} [Field k] [Finite k] (J : HermitianForm 3 k) {f : ℕ}
    (hf : 2 ≤ f) (hcard : Nat.card k = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : k // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    normalizer ((hermitianUnipotentPSU J hJ).range : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      unitaryCoordinateStabilizer J 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hnormal, -, hUT, -, -, -, ⟨S, hS⟩, hUcard, -, hSE,
    -⟩ := unitary_three_point_structure J f hf hcard hfixed hJ
  have hUB : (hermitianUnipotentPSU J hJ).range ≤ unitaryCoordinateStabilizer J 0 :=
    hUT ▸ le_sup_left
  refine le_antisymm (normalizer_le_of_stronglyEmbedded hSE (hS ▸ S.isPGroup') ?_ hUB)
    ((normal_subgroupOf_iff_le_normalizer hUB).1 hnormal)
  intro h
  rw [h, card_bot] at hUcard
  have : 1 < (2 ^ f) ^ 3 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
  omega

variable {A : Type*} [Group A] [Finite A]

theorem borel_eq_of_isCoatom {K S B : Subgroup A} [K.Normal] {U' : Subgroup K}
    (hU' : U' = (S ⊓ K).subgroupOf K) (hU2 : IsPGroup 2 U') (hidx : ¬ 2 ∣ U'.index)
    (hco : IsCoatom (normalizer (U' : Set K))) (hKS : K ⊔ S = ⊤) (hSB : S ≤ B) (hBtop : B < ⊤)
    (hBmax : ∀ Y : Subgroup A, S ≤ Y → Y < ⊤ → Y ≤ B) :
    B ⊓ K = (normalizer (U' : Set K)).map K.subtype ∧
      B ≤ normalizer ((S ⊓ K : Subgroup A) : Set A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := S ⊓ K with hUdef
  have hUK : U ≤ K := inf_le_right
  have hNmap : (normalizer (U' : Set K)).map K.subtype = K ⊓ normalizer (U : Set A) := by
    rw [hU', ← inf_normalizer_subgroupOf hUK, map_subgroupOf_eq_of_le inf_le_left]
  have hSN : S ≤ normalizer (U : Set A) := by
    intro s hs
    refine mem_normalizer_iff.2 fun y => ⟨fun hy => ⟨?_, ?_⟩, fun hy => ⟨?_, ?_⟩⟩
    · exact S.mul_mem (S.mul_mem hs hy.1) (S.inv_mem hs)
    · exact (‹K.Normal›).conj_mem y hy.2 s
    · have h1 := S.mul_mem (S.mul_mem (S.inv_mem hs) hy.1) hs
      rwa [show s⁻¹ * (s * y * s⁻¹) * s = y by group] at h1
    · have h1 := (‹K.Normal›).conj_mem _ hy.2 s⁻¹
      rwa [show s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ = y by group] at h1
  have hNtop : normalizer (U : Set A) ≠ ⊤ := by
    intro htop
    apply hco.1
    rw [eq_top_iff]
    intro y _
    have h1 : (y : A) ∈ K ⊓ normalizer (U : Set A) := ⟨y.2, htop ▸ mem_top _⟩
    rw [← hNmap] at h1
    obtain ⟨z, hz, hzy⟩ := h1
    rwa [← K.subtype_injective hzy]
  have hNB : normalizer (U : Set A) ≤ B := hBmax _ hSN (lt_top_iff_ne_top.2 hNtop)
  have hle : normalizer (U' : Set K) ≤ (B ⊓ K).subgroupOf K := by
    intro y hy
    have h1 : (y : A) ∈ (normalizer (U' : Set K)).map K.subtype := ⟨y, hy, rfl⟩
    rw [hNmap] at h1
    exact ⟨hNB h1.2, y.2⟩
  have hne : (B ⊓ K).subgroupOf K ≠ ⊤ := by
    intro h
    have hKB : K ≤ B := fun y hy => by
      have : (⟨y, hy⟩ : K) ∈ (B ⊓ K).subgroupOf K := h ▸ mem_top _
      exact this.1
    exact hBtop.ne (eq_top_iff.2 (hKS ▸ sup_le hKB hSB))
  have hBK : (B ⊓ K).subgroupOf K = normalizer (U' : Set K) := by
    rcases hco.le_iff.1 hle with h | h
    · exact absurd h hne
    · exact h
  have hBKeq : B ⊓ K = (normalizer (U' : Set K)).map K.subtype := by
    rw [← hBK, subgroupOf_map_subtype, inf_assoc, inf_idem]
  refine ⟨hBKeq, fun b hb => ?_⟩
  have hU2' : IsPGroup 2 U := by
    have h1 := hU2.map K.subtype
    rwa [hU', map_subgroupOf_eq_of_le hUK] at h1
  have hUidx : ¬ 2 ∣ U.relIndex K := by
    rwa [hU', ← relIndex] at hidx
  set P := U.map (MulAut.conj b).toMonoidHom with hPdef
  have hPBK : P ≤ K ⊓ normalizer (U : Set A) := by
    rw [← hNmap, ← hBKeq]
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨B.mul_mem (B.mul_mem hb (hSB hu.1)) (B.inv_mem hb), (‹K.Normal›).conj_mem u hu.2 b⟩
  have hUle : U ≤ K ⊓ normalizer (U : Set A) := le_inf hUK le_normalizer
  have hidx' : ¬ 2 ∣ U.relIndex (K ⊓ normalizer (U : Set A)) := fun h => hUidx
    (h.trans (Dvd.intro _ (relIndex_mul_relIndex U _ K hUle inf_le_left)))
  have hPU : P ≤ U := le_of_isPGroup_of_not_dvd_relIndex hU2' hUle hidx' (hU2'.map _) hPBK
    (hPBK.trans inf_le_right)
  have hPeq : P = U := eq_of_le_of_card_ge hPU (by
    rw [hPdef, card_map_of_injective (f := (MulAut.conj b).toMonoidHom)
      (MulAut.conj b).injective])
  refine mem_normalizer_iff.2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · rw [← hPeq]
    exact ⟨y, hy, rfl⟩
  · rw [← hPeq] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy
    have : z = y := by
      have h1 := congrArg (fun w => b⁻¹ * w * b) hzy
      simpa [mul_assoc] using h1
    rwa [← this]

theorem pCore_le_of_unitary {K S B : Subgroup A} [K.Normal]
    (hCK : ∀ a : A, (∀ x ∈ K, a * x = x * a) → a = 1) (hS2 : IsPGroup 2 S) (hSB : S ≤ B)
    {U₁ : Subgroup K} (hU₁ : U₁ = (S ⊓ K).subgroupOf K) (hUidx : ¬ 2 ∣ U₁.index)
    (hBK : B ⊓ K = (normalizer (U₁ : Set K)).map K.subtype)
    (hBN : B ≤ normalizer ((S ⊓ K : Subgroup A) : Set A))
    {k : Type} [Field k] [Finite k] (J : HermitianForm 3 k) {f : ℕ} (hf : 2 ≤ f)
    (hcard : Nat.card k = (2 ^ f) ^ 2) (hfixed : Nat.card {x : k // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (θ : K ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hθU : U₁.map θ.toMonoidHom = (hermitianUnipotentPSU J hJ).range)
    (hθN : (normalizer (U₁ : Set K)).map θ.toMonoidHom = unitaryCoordinateStabilizer J 0) :
    inSubgroup (pCore 2) B ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hUT, -⟩ :=
    unitary_three_point_structure J f hf hcard hfixed hJ
  have hTB : ∀ c : kˣ, torusPSU J hJ c ∈ unitaryCoordinateStabilizer J 0 := fun c => by
    rw [← hUT]
    exact mem_sup_right ⟨c, rfl⟩
  have hUidx' : ¬ 2 ∣ (S ⊓ K).relIndex K := by rwa [hU₁, ← relIndex] at hUidx
  have hR2 : IsPGroup 2 (inSubgroup (pCore 2) B) := (pCore_isPGroup (p := 2) (G := B)).map _
  have hRKU : inSubgroup (pCore 2) B ⊓ K ≤ S ⊓ K := by
    refine le_of_isPGroup_of_not_dvd_relIndex hS2.to_inf_left (inf_le_inf_right K hSB)
      (fun h => hUidx' (h.trans (Dvd.intro _ (relIndex_mul_relIndex (S ⊓ K) (B ⊓ K) K
        (inf_le_inf_right K hSB) inf_le_right)))) hR2.to_inf_left
      (inf_le_inf_right K (map_subtype_le _)) ?_
    exact inf_le_left.trans ((map_subtype_le _).trans hBN)
  have hRn : B ≤ normalizer (inSubgroup (pCore 2) B : Set A) :=
    le_normalizer.trans (normalizer_le_normalizer_map_characteristic B (pCore 2 B))
  have hmemN : ∀ y : K, y ∈ normalizer (U₁ : Set K) ↔ (y : A) ∈ B ⊓ K := fun y => by
    rw [hBK]
    exact ⟨fun hy => ⟨y, hy, rfl⟩, fun ⟨z, hz, hzy⟩ => K.subtype_injective hzy ▸ hz⟩
  have hθmem : ∀ (X : Subgroup K) (y : K), θ y ∈ X.map θ.toMonoidHom ↔ y ∈ X := fun X y => by
    rw [mem_map_equiv, MulEquiv.symm_apply_apply]
  intro r hr
  have hrB : r ∈ B := map_subtype_le _ hr
  set φ : A →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
    (MulAut.congr θ).toMonoidHom.comp MulAut.conjNormal with hφdef
  have hφ : ∀ (a : A) (y : K), φ a (θ y) = θ (MulAut.conjNormal a y) := fun a y => by
    simp [hφdef]
  have hconj : ∀ y : K, ((MulAut.conjNormal r y : K) : A) = r * y * r⁻¹ :=
    fun y => MulAut.conjNormal_apply r y
  have hβB : ∀ x ∈ unitaryCoordinateStabilizer J 0,
      φ r x ∈ unitaryCoordinateStabilizer J 0 := by
    intro x hx
    rw [← θ.apply_symm_apply x, hφ, ← hθN, hθmem, hmemN]
    rw [← hθN, ← θ.apply_symm_apply x, hθmem, hmemN] at hx
    rw [hconj]
    exact ⟨B.mul_mem (B.mul_mem hrB hx.1) (B.inv_mem hrB), (‹K.Normal›).conj_mem _ hx.2 r⟩
  have hβT : ∀ c : kˣ, φ r (torusPSU J hJ c) * (torusPSU J hJ c)⁻¹ ∈
      (hermitianUnipotentPSU J hJ).range := by
    intro c
    have hy := hTB c
    rw [← hθN, ← θ.apply_symm_apply (torusPSU J hJ c), hθmem, hmemN] at hy
    set y := θ.symm (torusPSU J hJ c) with hydef
    rw [← θ.apply_symm_apply (torusPSU J hJ c), hφ, ← map_inv, ← map_mul, ← hθU, hθmem, hU₁,
      mem_subgroupOf]
    have hcoe : ((MulAut.conjNormal r y * y⁻¹ : K) : A) = r * ((y : A) * r⁻¹ * (y : A)⁻¹) := by
      rw [coe_mul, hconj, coe_inv]
      group
    refine hRKU ⟨?_, (MulAut.conjNormal r y * y⁻¹).2⟩
    rw [hcoe]
    exact (inSubgroup (pCore 2) B).mul_mem hr ((mem_normalizer_iff.1 (hRn hy.1) r⁻¹).1
      ((inSubgroup (pCore 2) B).inv_mem hr))
  obtain ⟨m, hm⟩ := hR2 ⟨r, hr⟩
  have hrm : r ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hβk : φ r ^ 2 ^ m = 1 := by rw [← map_pow, hrm, map_one]
  obtain ⟨g, hg⟩ := exists_inner J hf hcard hfixed hJ hβB hβT hβk
  set y₀ := θ.symm g with hy₀
  have hcomm : ∀ z ∈ K, r * z * r⁻¹ = (y₀ : A) * z * (y₀ : A)⁻¹ := by
    intro z hz
    have h1 := hg (θ ⟨z, hz⟩)
    rw [hφ] at h1
    have h2 : MulAut.conjNormal r ⟨z, hz⟩ = y₀ * ⟨z, hz⟩ * y₀⁻¹ := by
      apply θ.injective
      rw [h1, map_mul, map_mul, map_inv, hy₀, θ.apply_symm_apply]
    have h3 := congrArg Subtype.val h2
    rw [hconj] at h3
    simpa using h3
  have ha := hCK ((y₀ : A)⁻¹ * r) fun z hz => by
    calc (y₀ : A)⁻¹ * r * z = (y₀ : A)⁻¹ * (r * z * r⁻¹) * r := by group
      _ = (y₀ : A)⁻¹ * ((y₀ : A) * z * (y₀ : A)⁻¹) * r := by rw [hcomm z hz]
      _ = z * ((y₀ : A)⁻¹ * r) := by group
  rw [← inv_mul_eq_one.mp ha]
  exact y₀.2

end CFSG.Quasithin.Ch3E213M.P4C
