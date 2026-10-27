module

public import CFSG.LocalAnalysis.StandardType.GGFieldOuterNormalForm
import CFSG.LieType.AschbacherSeitz.F4GraphFieldInvolution
import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizerF4
import CFSG.LieType.Chevalley.LangQuadraticFieldCosetConjugacy
import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
import CFSG.LocalAnalysis.SeitzReduction.Fusion

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem f4_iform_single_zero :
    iform (τ := ReeTag.F4.tag) (Pi.single (0 : Fin 4) 1) (Pi.single (3 : Fin 4) 1) = 0 := by
  decide +kernel

private theorem f4_not_isRoot_single_add :
    ¬ IsRoot ReeTag.F4.tag (Pi.single (0 : Fin 4) 1 + Pi.single (3 : Fin 4) 1) := by
  simp only [RootCertificate.isRoot_iff (Tag.rootCertificate_check ReeTag.F4.tag)]
  decide +kernel

private theorem f4_pinnedX_entrywise
    {K : Type} [Field K] {σ : K ≃+* K}
    (α : Fin ReeTag.F4.tag.rank → ℤ) (c : K) :
    Units.map (entrywiseHom σ.toRingHom) (pinnedX ReeTag.F4.tag K α c) =
      pinnedX ReeTag.F4.tag K α (σ c) := by
  apply Units.ext
  rw [Units.coe_map]
  change entrywise σ.toRingHom
    (pinnedX ReeTag.F4.tag K α c : Module.End K (RootModule ReeTag.F4.tag K)) =
      pinnedX ReeTag.F4.tag K α (σ c)
  rw [entrywise_pinnedX]
  rfl

private theorem f4_perm_zero : ReeTag.F4.perm (0 : Fin 4) = (3 : Fin 4) := rfl

private theorem f4_dualRoot_zero :
    ReeTag.F4.dualRoot (Pi.single (0 : Fin 4) 1) = Pi.single (3 : Fin 4) 1 := by
  rw [ReeTag.dualRoot_single ReeTag.F4 (0 : Fin 4), f4_perm_zero]
  rfl


private theorem f4_pinnedX_commute {K : Type} [Field K] (x y : K) :
    pinnedX ReeTag.F4.tag K (Pi.single (3 : Fin 4) 1) x *
        pinnedX ReeTag.F4.tag K (Pi.single (0 : Fin 4) 1) y =
      pinnedX ReeTag.F4.tag K (Pi.single (0 : Fin 4) 1) y *
        pinnedX ReeTag.F4.tag K (Pi.single (3 : Fin 4) 1) x :=
  pinnedX_commute_of_iform_eq_zero K (isRoot_single _ _) (isRoot_single _ _)
    (by rw [iform_comm]; exact f4_iform_single_zero)
    (by rw [add_comm]; exact f4_not_isRoot_single_add) x y

private theorem f4_frame_mul {K : Type} [Field K] (a₁ a₄ b₁ b₄ : K) :
    (pinnedX ReeTag.F4.tag K (Pi.single (0 : Fin 4) 1) a₁ *
        pinnedX ReeTag.F4.tag K (Pi.single (3 : Fin 4) 1) a₄)⁻¹ *
      (pinnedX ReeTag.F4.tag K (Pi.single (0 : Fin 4) 1) b₁ *
        pinnedX ReeTag.F4.tag K (Pi.single (3 : Fin 4) 1) b₄) =
      pinnedX ReeTag.F4.tag K (Pi.single (0 : Fin 4) 1) (b₁ - a₁) *
        pinnedX ReeTag.F4.tag K (Pi.single (3 : Fin 4) 1) (b₄ - a₄) := by
  set P₁ : K → ModGL ReeTag.F4.tag K :=
    pinnedX ReeTag.F4.tag K (Pi.single (0 : Fin 4) 1) with hP₁
  set P₄ : K → ModGL ReeTag.F4.tag K :=
    pinnedX ReeTag.F4.tag K (Pi.single (3 : Fin 4) 1) with hP₄
  have hadd₁ : ∀ c d : K, P₁ (c + d) = P₁ c * P₁ d := by
    intro c d
    rw [hP₁]
    exact pinnedX_add ReeTag.F4.tag K (Pi.single (0 : Fin 4) 1) c d
  have hadd₄ : ∀ c d : K, P₄ (c + d) = P₄ c * P₄ d := by
    intro c d
    rw [hP₄]
    exact pinnedX_add ReeTag.F4.tag K (Pi.single (3 : Fin 4) 1) c d
  have hneg₁ : ∀ c : K, (P₁ c)⁻¹ = P₁ (-c) := by
    intro c
    rw [hP₁]
    exact pinnedX_neg ReeTag.F4.tag K (Pi.single (0 : Fin 4) 1) c
  have hneg₄ : ∀ c : K, (P₄ c)⁻¹ = P₄ (-c) := by
    intro c
    rw [hP₄]
    exact pinnedX_neg ReeTag.F4.tag K (Pi.single (3 : Fin 4) 1) c
  have hcomm : ∀ x y : K, P₄ x * P₁ y = P₁ y * P₄ x := by
    intro x y
    rw [hP₄, hP₁]
    exact f4_pinnedX_commute x y
  calc (P₁ a₁ * P₄ a₄)⁻¹ * (P₁ b₁ * P₄ b₄)
      = P₄ (-a₄) * P₁ (-a₁) * (P₁ b₁ * P₄ b₄) := by rw [mul_inv_rev, hneg₄, hneg₁]
    _ = P₄ (-a₄) * (P₁ (-a₁) * P₁ b₁) * P₄ b₄ := by group
    _ = P₄ (-a₄) * P₁ (b₁ - a₁) * P₄ b₄ := by
        rw [← hadd₁, show -a₁ + b₁ = b₁ - a₁ by ring]
    _ = P₁ (b₁ - a₁) * P₄ (-a₄) * P₄ b₄ := by rw [hcomm]
    _ = P₁ (b₁ - a₁) * (P₄ (-a₄) * P₄ b₄) := by group
    _ = P₁ (b₁ - a₁) * P₄ (b₄ - a₄) := by
        rw [← hadd₄, show -a₄ + b₄ = b₄ - a₄ by ring]

private theorem f4_even_case {f : ℕ} (hf : 1 ≤ f) (hfe : Even f) {K : Type} [Field K]
    [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) (α : MulAut (adjointGroup .F4 K))
    (h2 : α * α = 1) (hout : ∀ c : adjointGroup .F4 K, α ≠ MulAut.conj c) :
    ∃ (ψ : MulAut (adjointGroup .F4 K)) (x : adjointGroup .F4 K) (d₁ d₄ : Kˣ),
      ((ψ ((α x)⁻¹ * x) : adjointGroup .F4 K) : ModGL .F4 K) =
        pinnedX .F4 K (Pi.single (0 : Fin 4) 1) (d₁ : K) *
          pinnedX .F4 K (Pi.single (3 : Fin 4) 1) (d₄ : K) := by
  let αR : MulAut (adjointGroup ReeTag.F4.tag K) := α
  change ∃ (ψ : MulAut (adjointGroup ReeTag.F4.tag K)) (x : adjointGroup ReeTag.F4.tag K)
      (d₁ d₄ : Kˣ),
      ((ψ ((αR x)⁻¹ * x) : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) =
        pinnedX ReeTag.F4.tag K (Pi.single (0 : Fin 4) 1) (d₁ : K) *
          pinnedX ReeTag.F4.tag K (Pi.single (3 : Fin 4) 1) (d₄ : K)
  have h2R : αR * αR = 1 := h2
  have houtR : ∀ c : adjointGroup ReeTag.F4.tag K, αR ≠ MulAut.conj c := hout
  classical
  obtain ⟨e, g, hf2, hαeq⟩ :=
    CFSG.StandardType.ggFieldOuterNormalForm_F4 hf hfe hK αR h2R houtR
  have he : 1 ≤ e := by omega
  have hK2 : Nat.card K = 2 ^ (2 * e) := by rw [hK, hf2]
  have hK' : Nat.card K = (2 ^ e) ^ 2 := by rw [hK2, mul_comm 2 e, pow_mul]
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 e
  have hσ : ∀ c, σ c = c ^ 2 ^ e := fun c => iterateFrobeniusEquiv_def K 2 e c
  have hσeq : entrywiseAdjointAut ReeTag.F4.tag σ = ReeTag.F4.finiteFrobeniusAut K ^ e :=
    entrywiseAdjointAut_eq_finiteFrobeniusAut_pow hσ
  have hαeq' : αR = MulAut.conj g * entrywiseAdjointAut ReeTag.F4.tag σ := by
    rw [hαeq, ← hσeq]
  have hexpr : ∀ u : adjointGroup ReeTag.F4.tag K,
      (αR u : ModGL ReeTag.F4.tag K) =
        (g : ModGL ReeTag.F4.tag K) *
          rootDiagUnit ReeTag.F4.tag (1 : Fin ReeTag.F4.tag.rank → Kˣ) *
            Units.map (entrywiseHom σ.toRingHom) (u : ModGL ReeTag.F4.tag K) *
              (rootDiagUnit ReeTag.F4.tag (1 : Fin ReeTag.F4.tag.rank → Kˣ))⁻¹ *
                (g : ModGL ReeTag.F4.tag K)⁻¹ := by
    intro u
    rw [hαeq']
    simp only [MulAut.mul_apply, MulAut.conj_apply, coe_entrywiseAdjointAut,
      rootDiagUnit_one, Subgroup.coe_mul, Subgroup.coe_inv, mul_one, inv_one]
  obtain ⟨β, -, hcos⟩ :=
    (exceptional_Lang_quadratic_field_coset_conjugacy Nat.prime_two he K hK' σ.toRingHom hσ).1
      ReeTag.F4.tag
  obtain ⟨ψ, hψ, -⟩ := (hcos g (1 : Fin ReeTag.F4.tag.rank → Kˣ)).2 αR hexpr h2R
  obtain ⟨c, hc⟩ : ∃ c : K, c ^ 2 ^ e ≠ c := by
    by_contra! h
    have hle := CFSG.SeitzReduction.natCard_le_of_forall_pow_eq_self
      (Nat.one_lt_two_pow (by omega : e ≠ 0)) (Set.univ : Set K) fun a _ => h a
    rw [Nat.card_univ, hK2] at hle
    have hlt : 2 ^ e < 2 ^ (2 * e) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hd : c - σ c ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact hc (by rw [← hσ c]; exact h.symm)
  let u : adjointGroup ReeTag.F4.tag K :=
    ⟨pinnedX ReeTag.F4.tag K (Pi.single (0 : Fin 4) 1) c, pinnedX_mem_adjointGroup _ _⟩ *
      ⟨pinnedX ReeTag.F4.tag K (Pi.single (3 : Fin 4) 1) c, pinnedX_mem_adjointGroup _ _⟩
  let x : adjointGroup ReeTag.F4.tag K := ψ⁻¹ u
  let d : Kˣ := Units.mk0 (c - σ c) hd
  refine ⟨ψ, x, d, d, ?_⟩
  have hψx : ψ x = u := by simp [x]
  have hψαx : ψ (αR x) = (ψ * αR * ψ⁻¹) u := by simp [x]
  have h1 : ((ψ (αR x) : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) =
      Units.map (entrywiseHom σ.toRingHom) (u : ModGL ReeTag.F4.tag K) := by
    rw [hψαx]
    exact hψ u
  have h2' : ((ψ x : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) =
      (u : ModGL ReeTag.F4.tag K) := by rw [hψx]
  have hstep : ((ψ ((αR x)⁻¹ * x) : adjointGroup ReeTag.F4.tag K) :
        ModGL ReeTag.F4.tag K) =
      ((ψ (αR x) : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K)⁻¹ *
        ((ψ x : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) := by
    rw [map_mul, map_inv]
    rfl
  rw [hstep, h1, h2']
  have hu : (u : ModGL ReeTag.F4.tag K) =
      pinnedX ReeTag.F4.tag K (Pi.single (0 : Fin 4) 1) c *
        pinnedX ReeTag.F4.tag K (Pi.single (3 : Fin 4) 1) c := rfl
  rw [hu, map_mul, f4_pinnedX_entrywise, f4_pinnedX_entrywise, f4_frame_mul]
  have harg : (d : K) = c - σ c := Units.val_mk0 hd
  simp only [harg]

private theorem f4_odd_case {f m : ℕ} (hf : 1 ≤ f) (hm : f = 2 * m + 1) {K : Type} [Field K]
    [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) (α : MulAut (adjointGroup .F4 K))
    (h2 : α * α = 1) (hout : ∀ c : adjointGroup .F4 K, α ≠ MulAut.conj c) :
    ∃ (ψ : MulAut (adjointGroup .F4 K)) (x : adjointGroup .F4 K) (d₁ d₄ : Kˣ),
      ((ψ ((α x)⁻¹ * x) : adjointGroup .F4 K) : ModGL .F4 K) =
        pinnedX .F4 K (Pi.single (0 : Fin 4) 1) (d₁ : K) *
          pinnedX .F4 K (Pi.single (3 : Fin 4) 1) (d₄ : K) := by
  let αR : MulAut (adjointGroup ReeTag.F4.tag K) := α
  change ∃ (ψ : MulAut (adjointGroup ReeTag.F4.tag K)) (x : adjointGroup ReeTag.F4.tag K)
      (d₁ d₄ : Kˣ),
      ((ψ ((αR x)⁻¹ * x) : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) =
        pinnedX ReeTag.F4.tag K (Pi.single (0 : Fin 4) 1) (d₁ : K) *
          pinnedX ReeTag.F4.tag K (Pi.single (3 : Fin 4) 1) (d₄ : K)
  have h2R : αR * αR = 1 := h2
  have houtR : ∀ c : adjointGroup ReeTag.F4.tag K, αR ≠ MulAut.conj c := hout
  classical
  have hα2 : αR ^ 2 = 1 := by rwa [pow_two]
  have hout' : αR ∉ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
      MulAut (adjointGroup ReeTag.F4.tag K)).range := by
    rintro ⟨c, hc⟩
    exact houtR c hc.symm
  obtain ⟨h, hαeq⟩ :=
    CFSG.LieType.AschbacherSeitz.exists_eq_conj_mul_finiteReeAut_of_involution hf K hK hm hα2
      hout'
  have hFF : ReeTag.F4.finiteReeAut K m * ReeTag.F4.finiteReeAut K m = 1 :=
    ReeTag.finiteReeAut_mul_self (t := ReeTag.F4) (K := K) (a := m) (by rw [hK, hm]; rfl)
  have hFinv : (ReeTag.F4.finiteReeAut K m)⁻¹ = ReeTag.F4.finiteReeAut K m :=
    inv_eq_of_mul_eq_one_right hFF
  have hconjAut : ∀ x : adjointGroup ReeTag.F4.tag K,
      MulAut.conj (ReeTag.F4.finiteReeAut K m x) =
        ReeTag.F4.finiteReeAut K m * MulAut.conj x * (ReeTag.F4.finiteReeAut K m)⁻¹ := by
    intro x
    ext y
    simp [MulAut.conj_apply, map_mul, map_inv]
  have hconj1 : MulAut.conj (h * ReeTag.F4.finiteReeAut K m h) = 1 := by
    rw [map_mul, hconjAut h, hFinv]
    calc MulAut.conj h *
          (ReeTag.F4.finiteReeAut K m * MulAut.conj h * ReeTag.F4.finiteReeAut K m) =
        (MulAut.conj h * ReeTag.F4.finiteReeAut K m) *
          (MulAut.conj h * ReeTag.F4.finiteReeAut K m) := by group
      _ = αR * αR := by rw [hαeq]
      _ = 1 := h2R
  have hcenter : h * ReeTag.F4.finiteReeAut K m h ∈
      Subgroup.center (adjointGroup ReeTag.F4.tag K) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := DFunLike.congr_fun hconj1 x
    simp only [MulAut.conj_apply, MulAut.one_apply] at hx
    have hzx : (h * ReeTag.F4.finiteReeAut K m h) * x =
        x * (h * ReeTag.F4.finiteReeAut K m h) := by
      calc (h * ReeTag.F4.finiteReeAut K m h) * x =
            ((h * ReeTag.F4.finiteReeAut K m h) * x *
              (h * ReeTag.F4.finiteReeAut K m h)⁻¹) *
              (h * ReeTag.F4.finiteReeAut K m h) := by group
        _ = x * (h * ReeTag.F4.finiteReeAut K m h) := by rw [hx]
    exact hzx.symm
  have hz1 : h * ReeTag.F4.finiteReeAut K m h = 1 := by
    have hmem := hcenter
    rw [center_adjointGroup_eq_bot] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hFh : ReeTag.F4.finiteReeAut K m h = h⁻¹ := eq_inv_of_mul_eq_one_right hz1
  obtain ⟨u, hu⟩ := CFSG.LieType.AschbacherSeitz.exists_eq_inv_mul_finiteReeAut_of_eq_inv
    (K := K) (m := m) (by rw [hK, hm]) hFh
  have hconjinv : (MulAut.conj (u⁻¹))⁻¹ = MulAut.conj u := by simp only [map_inv, inv_inv]
  have hαv : αR = MulAut.conj (u⁻¹) * ReeTag.F4.finiteReeAut K m *
      (MulAut.conj (u⁻¹))⁻¹ := by
    rw [hαeq, hu, map_mul, hconjAut u, hconjinv]
    group
  let cj : MulAut (adjointGroup ReeTag.F4.tag K) := MulAut.conj (u⁻¹)
  have hαv' : cj⁻¹ * αR * cj = ReeTag.F4.finiteReeAut K m := by
    have h : (MulAut.conj (u⁻¹))⁻¹ * αR * MulAut.conj (u⁻¹) =
        ReeTag.F4.finiteReeAut K m := by
      rw [hαv]
      group
    exact h
  let u₀ : adjointGroup ReeTag.F4.tag K :=
    ⟨pinnedX ReeTag.F4.tag K (Pi.single (0 : Fin 4) 1) 1, pinnedX_mem_adjointGroup _ _⟩
  let u₁ : adjointGroup ReeTag.F4.tag K :=
    ⟨pinnedX ReeTag.F4.tag K (Pi.single (3 : Fin 4) 1) 1, pinnedX_mem_adjointGroup _ _⟩
  refine ⟨cj⁻¹, cj u₀, 1, 1, ?_⟩
  have hψαx : cj⁻¹ (αR (cj u₀)) = ReeTag.F4.finiteReeAut K m u₀ := by
    have h : (cj⁻¹ * αR * cj) u₀ = ReeTag.F4.finiteReeAut K m u₀ := by rw [hαv']
    simpa only [MulAut.mul_apply] using h
  have hψx : cj⁻¹ (cj u₀) = u₀ := by
    simpa only [MulAut.mul_apply, MulAut.one_apply] using
      congrArg (fun g : MulAut (adjointGroup ReeTag.F4.tag K) => g u₀) (inv_mul_cancel cj)
  have hFu₀ : ReeTag.F4.finiteReeAut K m u₀ = u₁ := by
    have h := ReeTag.finiteReeAut_pinnedX_F4 (K := K) (a := m)
      (α := Pi.single (0 : Fin 4) 1) (isRoot_single ReeTag.F4.tag (0 : Fin 4)) (1 : K)
    dsimp only [u₀, u₁]
    simp only [f4_dualRoot_zero, one_pow] at h
    exact h
  have hstep : ((cj⁻¹ ((αR (cj u₀))⁻¹ * (cj u₀)) : adjointGroup ReeTag.F4.tag K) :
        ModGL ReeTag.F4.tag K) =
      ((cj⁻¹ (αR (cj u₀)) : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K)⁻¹ *
        ((cj⁻¹ (cj u₀) : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) := by
    rw [map_mul, map_inv]
    rfl
  rw [hstep, hψαx, hψx, hFu₀]
  dsimp only [u₁, u₀]
  rw [pinnedX_neg, CharTwo.neg_eq]
  exact f4_pinnedX_commute 1 1

theorem f4_exists_inv_mul_eq_frame {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (α : MulAut (adjointGroup .F4 K)) (h2 : α * α = 1)
    (hout : ∀ c : adjointGroup .F4 K, α ≠ MulAut.conj c) :
    ∃ (ψ : MulAut (adjointGroup .F4 K)) (x : adjointGroup .F4 K) (d₁ d₄ : Kˣ),
      ((ψ ((α x)⁻¹ * x) : adjointGroup .F4 K) : ModGL .F4 K) =
        pinnedX .F4 K (Pi.single (0 : Fin 4) 1) (d₁ : K) *
          pinnedX .F4 K (Pi.single (3 : Fin 4) 1) (d₄ : K) := by
  classical
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (by norm_num) f).ne')
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  rcases Nat.even_or_odd f with hfe | hfo
  · exact f4_even_case hf hfe hK α h2 hout
  · obtain ⟨m, hm⟩ := hfo
    exact f4_odd_case hf hm hK α h2 hout

end CFSG.LocalAnalysis.WeakClosure81
