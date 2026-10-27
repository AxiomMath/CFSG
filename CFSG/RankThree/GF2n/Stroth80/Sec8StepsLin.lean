module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Module

theorem ker_sub_one_eq_orthogonal_range {F E : Type} [Field F] [AddCommGroup E] [Module F E]
    (β : LinearMap.BilinForm F E) (hnd : β.Nondegenerate) (hrefl : β.IsRefl)
    (x : E →ₗ[F] E) (hiso : ∀ u v, β (x u) (x v) = β u v) (hsurj : Function.Surjective x) :
    LinearMap.ker (x - 1) = β.orthogonal (LinearMap.range (x - 1)) := by
  have key : ∀ u v : E, β ((x - 1) u) v = β (x u) (v - x v) := by
    intro u v
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hiso]
  ext v
  constructor
  · intro hv
    have hxv : x v = v := by
      have h1 : (x - 1) v = x v - v := by simp
      rw [LinearMap.mem_ker, h1] at hv
      exact sub_eq_zero.mp hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    rintro n ⟨u, rfl⟩
    rw [key u v, hxv, sub_self, map_zero]
  · intro hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv
    have hw : v - x v = 0 := by
      apply hnd.2
      intro w
      obtain ⟨u, rfl⟩ := hsurj w
      rw [← key u v]
      exact hv _ (LinearMap.mem_range_self (x - 1) u)
    have h1 : (x - 1) v = x v - v := by simp
    rw [LinearMap.mem_ker, h1]
    exact sub_eq_zero.mpr (sub_eq_zero.mp hw).symm

theorem lemmaD_core {F E : Type} [Field F] [AddCommGroup E] [Module F E] [FiniteDimensional F E]
    (β : LinearMap.BilinForm F E) (hnd : β.Nondegenerate) (hrefl : β.IsRefl)
    (ψ : E →ₗ[F] E) (A : Submodule F E)
    (hker : LinearMap.ker ψ = β.orthogonal (LinearMap.range ψ))
    (hW : ∀ w ∈ β.orthogonal A, ψ w ∈ A) :
    finrank F (LinearMap.range ψ) ≤ 2 * finrank F (LinearMap.range ψ ⊓ A : Submodule F E) := by
  have hmap_le : (β.orthogonal A).map ψ ≤ LinearMap.range ψ ⊓ A := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hy
    exact Submodule.mem_inf.mpr ⟨LinearMap.mem_range_self ψ w, hW w hw⟩
  have hmono : finrank F ((β.orthogonal A).map ψ) ≤
      finrank F (LinearMap.range ψ ⊓ A : Submodule F E) :=
    Submodule.finrank_mono hmap_le
  have hperp : β.orthogonal A ⊓ LinearMap.ker ψ = β.orthogonal (A ⊔ LinearMap.range ψ) := by
    rw [hker]
    ext m
    simp only [Submodule.mem_inf, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · rintro ⟨h1, h2⟩ n hn
      obtain ⟨a, ha, r, hr, rfl⟩ := Submodule.mem_sup.mp hn
      rw [map_add, LinearMap.add_apply, h1 a ha, h2 r hr, add_zero]
    · intro h
      exact ⟨fun n hn => h n (Submodule.mem_sup_left hn),
        fun n hn => h n (Submodule.mem_sup_right hn)⟩
  have hrank := LinearMap.finrank_range_add_finrank_ker (ψ.domRestrict (β.orthogonal A))
  have hkerdr : (LinearMap.ker (ψ.domRestrict (β.orthogonal A))).map (β.orthogonal A).subtype =
      β.orthogonal A ⊓ LinearMap.ker ψ := by
    rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype]
  have hk : finrank F (LinearMap.ker (ψ.domRestrict (β.orthogonal A))) =
      finrank F (β.orthogonal A ⊓ LinearMap.ker ψ : Submodule F E) := by
    rw [← hkerdr, Submodule.finrank_map_subtype_eq]
  rw [LinearMap.range_domRestrict, hk] at hrank
  have hW_fin : finrank F (β.orthogonal A) = finrank F E - finrank F A :=
    LinearMap.BilinForm.finrank_orthogonal hnd A
  have hperp_fin : finrank F (β.orthogonal A ⊓ LinearMap.ker ψ : Submodule F E) =
      finrank F E - finrank F (A ⊔ LinearMap.range ψ : Submodule F E) := by
    rw [hperp]
    exact LinearMap.BilinForm.finrank_orthogonal hnd _
  have hsum : finrank F (A ⊔ LinearMap.range ψ : Submodule F E) +
      finrank F (LinearMap.range ψ ⊓ A : Submodule F E) =
      finrank F A + finrank F (LinearMap.range ψ : Submodule F E) := by
    rw [inf_comm]
    exact Submodule.finrank_sup_add_finrank_inf_eq A _
  have hle1 : finrank F (A ⊔ LinearMap.range ψ : Submodule F E) ≤ finrank F E :=
    Submodule.finrank_le _
  have hle2 : finrank F A ≤ finrank F E := Submodule.finrank_le _
  omega


theorem finrank_inf_sup_le_aux {F E : Type} [Field F] [AddCommGroup E] [Module F E]
    [FiniteDimensional F E] (P Q S : Submodule F E) :
    finrank F ↥((P ⊔ Q) ⊓ S) ≤ finrank F ↥(P ⊓ S) + finrank F ↥Q := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq ((P ⊔ Q) ⊓ S) P
  have h2 : ((P ⊔ Q) ⊓ S) ⊓ P ≤ P ⊓ S :=
    le_inf inf_le_right (inf_le_left.trans inf_le_right)
  have h3 : ((P ⊔ Q) ⊓ S) ⊔ P ≤ P ⊔ Q :=
    sup_le inf_le_left le_sup_left
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq P Q
  have h5 := Submodule.finrank_mono h2
  have h6 := Submodule.finrank_mono h3
  omega

theorem finrank_inf_le_of_codim_one {F E : Type} [Field F] [AddCommGroup E] [Module F E]
    [FiniteDimensional F E] (R A₀ A : Submodule F E) (hle : A₀ ≤ A)
    (hdim : finrank F A = finrank F A₀ + 1) :
    finrank F ↥(R ⊓ A) ≤ finrank F ↥(R ⊓ A₀) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (R ⊓ A) A₀
  have h2 : (R ⊓ A) ⊓ A₀ = R ⊓ A₀ := by
    ext x
    simp only [Submodule.mem_inf]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hle h.2⟩, h.2⟩⟩
  have h3 : (R ⊓ A) ⊔ A₀ ≤ A := sup_le inf_le_right hle
  have h4 := Submodule.finrank_mono h3
  rw [h2] at h1
  omega

theorem sec8_invol_core {K E : Type} [Field K] [CharP K 2] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (T : E →ₗ[K] E) (hT2 : ∀ e, T (T e) = e)
    (A₀ A : Submodule K E) (hle : A₀ ≤ A)
    (hdim : finrank K A = finrank K A₀ + 1)
    (hA : ∀ a ∈ A, T a ∈ A) (h0 : ∀ a ∈ A₀, T a = a) :
    ∀ a ∈ A, T a - a ∈ A₀ := by
  have hne : A₀ ≠ A := by
    intro h
    rw [h] at hdim
    omega
  have hex : ∃ w ∈ A, w ∉ A₀ := by
    by_contra hcon
    apply hne
    apply le_antisymm hle
    intro x hx
    by_contra hx'
    exact hcon ⟨x, hx, hx'⟩
  obtain ⟨w, hwA, hw⟩ := hex
  have hw0 : w ≠ 0 := by
    intro h
    apply hw
    rw [h]
    exact A₀.zero_mem
  have hle' : A₀ ⊔ Submodule.span K {w} ≤ A :=
    sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).mpr hwA)
  have hinf : A₀ ⊓ Submodule.span K {w} = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxA₀, hxs⟩ := Submodule.mem_inf.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxs
    by_cases hc : c = 0
    · rw [hc, zero_smul]
      exact Submodule.zero_mem _
    · exfalso
      apply hw
      have h' := A₀.smul_mem c⁻¹ hxA₀
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h'
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq A₀ (Submodule.span K {w})
  rw [hinf, finrank_bot, finrank_span_singleton hw0] at hfin
  have hsup : A₀ ⊔ Submodule.span K {w} = A :=
    Submodule.eq_of_le_of_finrank_eq hle' (by omega)
  have hTw : T w ∈ A₀ ⊔ Submodule.span K {w} := by
    rw [hsup]
    exact hA w hwA
  obtain ⟨a₀, ha₀, z, hz, hsum⟩ := Submodule.mem_sup.mp hTw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hcalc : w = a₀ + c • (a₀ + c • w) := by
    calc w = T (T w) := (hT2 w).symm
      _ = T (a₀ + c • w) := by rw [hsum]
      _ = a₀ + c • T w := by rw [map_add, map_smul, h0 a₀ ha₀]
      _ = a₀ + c • (a₀ + c • w) := by rw [← hsum]
  have hkey : (1 - c * c) • w = (1 + c) • a₀ := by
    linear_combination (norm := module) hcalc
  have hmem : (1 - c * c) • w ∈ A₀ := by
    rw [hkey]
    exact A₀.smul_mem (1 + c) ha₀
  have hcc : 1 - c * c = 0 := by
    by_contra hne0
    apply hw
    have h' := A₀.smul_mem (1 - c * c)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hne0, one_smul] at h'
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : (c - 1) * (c - 1) = 0 := by
    linear_combination (-1 : K) * hcc + (-(c - 1)) * h2
  have hc1 : c = 1 := sub_eq_zero.mp (mul_self_eq_zero.mp hsq)
  have hTa : T w - w = a₀ := by
    rw [← hsum, hc1, one_smul]
    abel
  intro v hv
  rw [← hsup] at hv
  obtain ⟨a₁, ha₁, z, hz, hsum2⟩ := Submodule.mem_sup.mp hv
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hz
  subst hsum2
  have hcomp : T (a₁ + r • w) - (a₁ + r • w) = r • (T w - w) := by
    rw [map_add, map_smul, h0 a₁ ha₁, smul_sub]
    abel
  rw [hcomp, hTa]
  exact A₀.smul_mem r ha₀

theorem thm111_core {F E : Type} [Field F] [AddCommGroup E] [Module F E] [FiniteDimensional F E]
    (β : LinearMap.BilinForm F E) (hnd : β.Nondegenerate) (hrefl : β.IsRefl)
    (X X' L : E →ₗ[F] E)
    (hXiso : ∀ u v, β (X u) (X v) = β u v) (hX'iso : ∀ u v, β (X' u) (X' v) = β u v)
    (hXs : Function.Surjective X) (hX's : Function.Surjective X')
    (haa : (X' - 1) ∘ₗ (X - 1) = 0)
    (hE'' : LinearMap.range (X' - 1) = (LinearMap.range (X - 1)).map L)
    (hdisj : LinearMap.range (X - 1) ⊓ LinearMap.range (X' - 1) = ⊥)
    (hL : Function.Injective L)
    (f : ℕ) (hf : 0 < f) (hdim : finrank F (LinearMap.range (X - 1)) = 4 * f)
    (S Bpt : Submodule F E) (hS : S ≤ β.orthogonal S) (hSdim : 2 * finrank F S = finrank F E)
    (hB : finrank F Bpt ≤ f)
    (hSe : ∀ s ∈ S, (X' * X - 1) s ∈ Bpt) (hSL : ∀ s ∈ S, (L - 1) s ∈ Bpt) :
    False := by
  have hcomp_iso : ∀ u v, β ((X' * X) u) ((X' * X) v) = β u v := by
    intro u v
    show β (X' (X u)) (X' (X v)) = β u v
    rw [hX'iso, hXiso]
  have hcomp_surj : Function.Surjective (X' * X) := by
    intro w
    obtain ⟨u, rfl⟩ := hX's w
    obtain ⟨v, rfl⟩ := hXs u
    exact ⟨v, rfl⟩
  have ha'a : (X' - 1) * (X - 1) = 0 := by
    rw [Module.End.mul_eq_comp]
    exact haa
  have hT : X' * X - 1 = (X - 1) + (X' - 1) := by
    calc X' * X - 1 = (X' - 1) + (X - 1) + (X' - 1) * (X - 1) := by
          simp only [sub_mul, mul_sub, one_mul, mul_one]
          abel
      _ = (X - 1) + (X' - 1) := by rw [ha'a, add_zero, add_comm]
  have hTapp : ∀ v, (X' * X - 1) v = (X - 1) v + (X' - 1) v := by
    intro v
    rw [hT, LinearMap.add_apply]
  have hrangeT_le : LinearMap.range (X' * X - 1) ≤
      LinearMap.range (X - 1) ⊔ LinearMap.range (X' - 1) := by
    intro x hx
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hx
    rw [hTapp u]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ u) (LinearMap.mem_range_self _ u)
  have hE2dim : finrank F (LinearMap.range (X' - 1)) = 4 * f := by
    rw [hE'', ← (Submodule.equivMapOfInjective L hL (LinearMap.range (X - 1))).finrank_eq,
      hdim]
  have hsupdim : finrank F ↥(LinearMap.range (X - 1) ⊔ LinearMap.range (X' - 1)) = 8 * f := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range (X - 1)) (LinearMap.range (X' - 1))
    rw [hdisj, finrank_bot, hdim, hE2dim] at h
    omega
  have hsuple : finrank F ↥(LinearMap.range (X - 1) ⊔ LinearMap.range (X' - 1)) ≤
      finrank F E :=
    Submodule.finrank_le _
  have hkerT_inf : LinearMap.ker (X' * X - 1) =
      LinearMap.ker (X - 1) ⊓ LinearMap.ker (X' - 1) := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_inf, hTapp]
    constructor
    · intro hv
      have hmem : (X - 1) v ∈ LinearMap.range (X - 1) ⊓ LinearMap.range (X' - 1) := by
        refine Submodule.mem_inf.mpr ⟨LinearMap.mem_range_self _ v, ?_⟩
        have hneg : (X - 1) v = -((X' - 1) v) := eq_neg_of_add_eq_zero_left hv
        rw [hneg]
        exact neg_mem (LinearMap.mem_range_self _ v)
      rw [hdisj, Submodule.mem_bot] at hmem
      refine ⟨hmem, ?_⟩
      rw [hmem, zero_add] at hv
      exact hv
    · rintro ⟨h1, h2⟩
      rw [h1, h2, add_zero]
  have hkerT : LinearMap.ker (X' * X - 1) =
      β.orthogonal (LinearMap.range (X - 1) ⊔ LinearMap.range (X' - 1)) := by
    rw [hkerT_inf, ker_sub_one_eq_orthogonal_range β hnd hrefl X hXiso hXs,
      ker_sub_one_eq_orthogonal_range β hnd hrefl X' hX'iso hX's]
    ext m
    simp only [Submodule.mem_inf, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · rintro ⟨h1, h2⟩ n hn
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hn
      rw [map_add, LinearMap.add_apply, h1 y hy, h2 z hz, add_zero]
    · intro h
      exact ⟨fun n hn => h n (Submodule.mem_sup_left hn),
        fun n hn => h n (Submodule.mem_sup_right hn)⟩
  have hkerdim : finrank F ↥(LinearMap.ker (X' * X - 1)) = finrank F E - 8 * f := by
    rw [hkerT, LinearMap.BilinForm.finrank_orthogonal hnd, hsupdim]
  have hrangeTdim : finrank F ↥(LinearMap.range (X' * X - 1)) = 8 * f := by
    have h := LinearMap.finrank_range_add_finrank_ker (X' * X - 1)
    omega
  have hS_rank : finrank F S ≤ f + finrank F ↥(S ⊓ LinearMap.ker (X' * X - 1)) := by
    have h := LinearMap.finrank_range_add_finrank_ker ((X' * X - 1).domRestrict S)
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
    have hmap : finrank F ↥(S.map (X' * X - 1)) ≤ finrank F ↥Bpt :=
      Submodule.finrank_mono (Submodule.map_le_iff_le_comap.mpr (fun s hs => hSe s hs))
    have hcomap : finrank F ↥((LinearMap.ker (X' * X - 1)).comap S.subtype) =
        finrank F ↥(S ⊓ LinearMap.ker (X' * X - 1)) := by
      rw [← Submodule.map_comap_subtype S (LinearMap.ker (X' * X - 1)),
        Submodule.finrank_map_subtype_eq]
    omega
  have hKT : LinearMap.ker (X' * X - 1) = β.orthogonal (LinearMap.range (X' * X - 1)) :=
    ker_sub_one_eq_orthogonal_range β hnd hrefl (X' * X) hcomp_iso hcomp_surj
  have hCs_le : S ⊓ LinearMap.ker (X' * X - 1) ≤
      β.orthogonal (LinearMap.range (X' * X - 1)) :=
    le_trans inf_le_right (le_of_eq hKT)
  have hrangeT_perp : LinearMap.range (X' * X - 1) ≤
      β.orthogonal (S ⊓ LinearMap.ker (X' * X - 1)) :=
    le_trans (LinearMap.BilinForm.le_orthogonal_orthogonal hrefl)
      (LinearMap.BilinForm.orthogonal_le hCs_le)
  have hS_perp : S ≤ β.orthogonal (S ⊓ LinearMap.ker (X' * X - 1)) :=
    le_trans hS (LinearMap.BilinForm.orthogonal_le inf_le_left)
  have hsup_dim : finrank F ↥(LinearMap.range (X' * X - 1) ⊔ S) ≤
      finrank F E - finrank F ↥(S ⊓ LinearMap.ker (X' * X - 1)) := by
    have h1 := Submodule.finrank_mono (sup_le hrangeT_perp hS_perp)
    rw [LinearMap.BilinForm.finrank_orthogonal hnd] at h1
    exact h1
  have hint_dim : 7 * f ≤ finrank F ↥(LinearMap.range (X' * X - 1) ⊓ S) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (X' * X - 1)) S
    omega
  have hsub8 : LinearMap.range (X' * X - 1) ⊓ S ≤
      (LinearMap.range (X - 1) ⊔ LinearMap.range (X' - 1)) ⊓ S := by
    intro x hx
    exact Submodule.mem_inf.mpr
      ⟨hrangeT_le (Submodule.mem_inf.mp hx).1, (Submodule.mem_inf.mp hx).2⟩
  have hG := finrank_inf_sup_le_aux (LinearMap.range (X - 1)) (LinearMap.range (X' - 1)) S
  have hmain : 3 * f ≤ finrank F ↥(LinearMap.range (X - 1) ⊓ S) := by
    have h1 := Submodule.finrank_mono hsub8
    omega
  have hupper : finrank F ↥(LinearMap.range (X - 1) ⊓ S) ≤ f := by
    have hinj : Function.Injective
        (LinearMap.codRestrict Bpt ((L - 1).domRestrict (LinearMap.range (X - 1) ⊓ S))
          (fun s => hSL s.1 (Submodule.mem_inf.mp s.2).2)) := by
      rw [injective_iff_map_eq_zero]
      rintro ⟨s, hs⟩ h0
      have hs1 : s ∈ LinearMap.range (X - 1) := (Submodule.mem_inf.mp hs).1
      have hLs : L s = s := by
        have h2 : (L - 1) s = 0 := congrArg Subtype.val h0
        rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h2
        exact h2
      have hsE2 : s ∈ LinearMap.range (X' - 1) := by
        rw [hE'']
        exact Submodule.mem_map.mpr ⟨s, hs1, hLs⟩
      have hs0 : s ∈ LinearMap.range (X - 1) ⊓ LinearMap.range (X' - 1) :=
        Submodule.mem_inf.mpr ⟨hs1, hsE2⟩
      rw [hdisj, Submodule.mem_bot] at hs0
      exact Subtype.ext hs0
    have h1 := LinearMap.finrank_le_finrank_of_injective hinj
    omega
  omega

end CFSG.RankThree.GF2n.Stroth80
