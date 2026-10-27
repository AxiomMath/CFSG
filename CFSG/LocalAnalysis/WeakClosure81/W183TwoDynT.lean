module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

theorem actsOnDynkinMod_bot_of_autAction {G : Type} [Group G] [Finite G] {K H L : Subgroup G}
    (hL : IsComponentModN K H L) {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (φ : ↥L →* X) (hφs : Function.Surjective φ) (hφk : ∀ k : ↥L, φ k = 1 ↔ (k : G) ∈ K)
    (α : ↥(H ⊓ Subgroup.normalizer (L : Set G)) →* MulAut X)
    (hα : ∀ (n : ↥(H ⊓ Subgroup.normalizer (L : Set G))) (l l' : ↥L),
      (n : G) * (l : G) * (n : G)⁻¹ = (l' : G) → α n (φ l) = φ l') {t : G} (htH : t ∈ H)
    (hDyn : ActsOnDynkinMod K L t) :
    ActsOnDynkinMod (⊥ : Subgroup ↥α.range)
      (((MulAut.conj : X →* MulAut X).range).subgroupOf α.range)
      (⟨α ⟨t, Subgroup.mem_inf.mpr ⟨htH, hDyn.1⟩⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩ :
        ↥α.range) := by
  have hKL : K ≤ L := hL.2.1
  have hLH : L ≤ H := hL.2.2.1
  have htN : t ∈ Subgroup.normalizer (L : Set G) := hDyn.1
  let A : ↥L →* ↥α.range :=
    (α.comp (Subgroup.inclusion (le_inf hLH le_normalizer))).codRestrict α.range
      (fun x => MonoidHom.mem_range.mpr ⟨Subgroup.inclusion (le_inf hLH le_normalizer) x, rfl⟩)
  let L' : Subgroup ↥α.range :=
    ((MulAut.conj : X →* MulAut X).range).subgroupOf α.range
  let τ : ↥α.range :=
    ⟨α ⟨t, Subgroup.mem_inf.mpr ⟨htH, htN⟩⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩
  change ActsOnDynkinMod (⊥ : Subgroup ↥α.range) L' τ
  have hA_apply : ∀ l : ↥L, (A l : MulAut X) =
      α ⟨(l : G), Subgroup.mem_inf.mpr ⟨hLH l.2, le_normalizer l.2⟩⟩ :=
    fun l => congrArg α (Subtype.ext rfl)
  have hA_conj : ∀ l : ↥L, (A l : MulAut X) = MulAut.conj (φ l) := by
    intro l
    ext x
    obtain ⟨l₀, rfl⟩ := hφs x
    have h := hα ⟨(l : G), Subgroup.mem_inf.mpr ⟨hLH l.2, le_normalizer l.2⟩⟩ l₀
      (l * l₀ * l⁻¹) rfl
    rw [hA_apply, h]
    simp only [map_mul, map_inv, MulAut.conj_apply]
  have hA_ker : ∀ l : ↥L, A l = 1 ↔ (l : G) ∈ K := by
    intro l
    rw [← hφk l]
    constructor
    · intro h
      have h1 : (A l : MulAut X) = 1 := by
        have := congrArg (fun y : ↥α.range => (y : MulAut X)) h
        simpa using this
      rw [hA_conj l] at h1
      have h' : MulAut.conj (φ l) = 1 := h1
      have hc : φ l ∈ Subgroup.center X := by
        rw [Subgroup.mem_center_iff]
        intro x
        have hx := congrArg (fun f : MulAut X => f x) h'
        simp only [MulAut.conj_apply, MulAut.one_apply] at hx
        have hx2 : φ l * x = x * φ l := by
          have := congrArg (fun y : X => y * φ l) hx
          simpa [mul_assoc] using this
        exact hx2.symm
      rw [hZ] at hc
      exact Subgroup.mem_bot.mp hc
    · intro h
      apply Subtype.ext
      rw [hA_conj l, h]
      simp
  have hA_range : A.range = L' := by
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_subgroupOf]
      rw [MonoidHom.mem_range] at hy
      obtain ⟨l, rfl⟩ := hy
      refine MonoidHom.mem_range.mpr ⟨φ l, ?_⟩
      exact (hA_conj l).symm
    · intro y hy
      rw [Subgroup.mem_subgroupOf] at hy
      rw [MonoidHom.mem_range] at hy
      obtain ⟨z, hz⟩ := hy
      obtain ⟨l, rfl⟩ := hφs z
      refine MonoidHom.mem_range.mpr ⟨l, ?_⟩
      apply Subtype.ext
      rw [hA_conj l]
      exact hz
  have hτ_val : (τ : MulAut X) = α ⟨t, Subgroup.mem_inf.mpr ⟨htH, htN⟩⟩ := rfl
  have hτ_conj : ∀ l : ↥L,
      A ⟨t * (l : G) * t⁻¹,
        (Subgroup.mem_set_normalizer_iff.mp htN (l : G)).mp l.2⟩ = τ * A l * τ⁻¹ := by
    intro l
    apply Subtype.ext
    rw [hA_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hτ_val, hA_apply]
    simp only [← map_mul, ← map_inv]
    exact congrArg α (Subtype.ext rfl)
  have hτ_conj_inv : ∀ l : ↥L,
      A ⟨t⁻¹ * (l : G) * t,
        (Subgroup.mem_set_normalizer_iff''.mp htN (l : G)).mp l.2⟩ = τ⁻¹ * A l * τ := by
    intro l
    have hmem : t⁻¹ * (l : G) * t ∈ L :=
      (Subgroup.mem_set_normalizer_iff''.mp htN (l : G)).mp l.2
    have h := hτ_conj ⟨t⁻¹ * (l : G) * t, hmem⟩
    have hsub : (⟨t * (t⁻¹ * (l : G) * t) * t⁻¹,
        (Subgroup.mem_set_normalizer_iff.mp htN (t⁻¹ * (l : G) * t)).mp hmem⟩ : ↥L) =
        ⟨(l : G), l.2⟩ := by
      ext; group
    rw [hsub] at h
    rw [show (⟨(l : G), l.2⟩ : ↥L) = l from rfl] at h
    rw [h]
    group
  have hτN : τ ∈ Subgroup.normalizer (L' : Set ↥α.range) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hA_range] at hx ⊢
      obtain ⟨l, rfl⟩ := MonoidHom.mem_range.mp hx
      rw [show τ * A l * τ⁻¹ = A ⟨t * (l : G) * t⁻¹,
        (Subgroup.mem_set_normalizer_iff.mp htN (l : G)).mp l.2⟩ from (hτ_conj l).symm]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    · intro hx
      rw [← hA_range] at hx ⊢
      obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp hx
      refine MonoidHom.mem_range.mpr ⟨⟨t⁻¹ * (l : G) * t,
        (Subgroup.mem_set_normalizer_iff''.mp htN (l : G)).mp l.2⟩, ?_⟩
      rw [hτ_conj_inv l, hl]
      group
  obtain ⟨P, hP, hconj⟩ := hDyn.2
  obtain ⟨hKP, hPLt, hPmax, S, hKS, hSL, hSpow, hSodd, hSnorm⟩ := hP
  let P₁ : Subgroup ↥L := P.subgroupOf L
  let P' : Subgroup ↥α.range := P₁.map A
  let S₁ : Subgroup ↥L := S.subgroupOf L
  let S' : Subgroup ↥α.range := S₁.map A
  have hPmap : P₁.map L.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPLt.le
  have hP'le : P' ≤ L' := (Subgroup.map_le_range (f := A) P₁).trans_eq hA_range
  have hP'lt : P' < L' := by
    refine lt_of_le_of_ne hP'le ?_
    intro heq
    have hle : L' ≤ P' := heq.ge
    have hLP : L ≤ P := by
      intro x hx
      have hxL' : A ⟨x, hx⟩ ∈ L' := by
        rw [← hA_range]
        exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
      obtain ⟨p, hp, hAp⟩ := Subgroup.mem_map.mp (hle hxL')
      have hpP : (p : G) ∈ P := hp
      have hpk : ((p⁻¹ * ⟨x, hx⟩ : ↥L) : G) ∈ K := by
        apply (hA_ker (p⁻¹ * ⟨x, hx⟩)).mp
        rw [map_mul, map_inv, hAp, inv_mul_cancel]
      rw [show x = (p : G) * ((p⁻¹ * ⟨x, hx⟩ : ↥L) : G) from by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group]
      exact P.mul_mem hpP (hKP hpk)
    exact hPLt.not_ge hLP
  have hP'max : ∀ Z : Subgroup ↥α.range, P' < Z → Z ≤ L' → Z = L' := by
    intro Z hPZ hZL'
    let Z₀ : Subgroup ↥L := Z.comap A
    have hZmap : Z₀.map A = Z := by
      change (Z.comap A).map A = Z
      rw [Subgroup.map_comap_eq, hA_range, inf_eq_right.mpr hZL']
    have hP₁Z₀ : P₁ ≤ Z₀ := fun p hp => hPZ.le (Subgroup.mem_map_of_mem A hp)
    have hZG_le : P ≤ Z₀.map L.subtype := by
      intro p hp
      exact Subgroup.mem_map.mpr ⟨⟨p, hPLt.le hp⟩,
        hP₁Z₀ (by rw [Subgroup.mem_subgroupOf]; exact hp), rfl⟩
    have hZG_leL : Z₀.map L.subtype ≤ L := Subgroup.map_subtype_le Z₀
    have hZG_lt : P < Z₀.map L.subtype := by
      refine lt_of_le_of_ne hZG_le ?_
      intro heq
      have hle : Z₀ ≤ P₁ := by
        have h1 : P₁.map L.subtype = Z₀.map L.subtype := by rw [hPmap, heq]
        exact (Subgroup.map_le_map_iff_of_injective L.subtype_injective).mp h1.ge
      have hZ0eq : Z₀ = P₁ := le_antisymm hle hP₁Z₀
      have : P' = Z := by
        change P₁.map A = Z
        rw [← hZ0eq, hZmap]
      exact hPZ.ne this
    have hZG_eq : Z₀.map L.subtype = L := hPmax _ hZG_lt hZG_leL
    have hZ₀top : Z₀ = ⊤ := by
      have hcomap : Subgroup.comap L.subtype L = ⊤ := by
        ext x
        exact ⟨fun _ => trivial, fun _ => x.2⟩
      have h := congrArg (Subgroup.comap L.subtype) hZG_eq
      rw [Subgroup.comap_map_eq_self_of_injective L.subtype_injective] at h
      rwa [hcomap] at h
    rw [← hZmap, hZ₀top, Subgroup.map_top, hA_range]
  have hS'le : S' ≤ L' := (Subgroup.map_le_range (f := A) S₁).trans_eq hA_range
  have hS'pow : ∀ s ∈ S', ∃ k : ℕ, s ^ 2 ^ k ∈ (⊥ : Subgroup ↥α.range) := by
    intro s hs
    obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨k, hk⟩ := hSpow (s₀ : G) (Subgroup.mem_subgroupOf.mp hs₀)
    refine ⟨k, ?_⟩
    rw [Subgroup.mem_bot, ← map_pow]
    exact (hA_ker (s₀ ^ 2 ^ k)).mpr (by rwa [Subgroup.coe_pow])
  have hS'odd : ¬ 2 ∣ S'.relIndex L' := by
    have hrel : S'.relIndex L' = S.relIndex L := by
      change (S₁.map A).relIndex L' = S.relIndex L
      have hL'top : L' = (⊤ : Subgroup ↥L).map A := by rw [Subgroup.map_top, hA_range]
      rw [hL'top, Subgroup.relIndex_map_map]
      have hker_le : A.ker ≤ S₁ := by
        intro k hk
        rw [Subgroup.mem_subgroupOf]
        exact hKS ((hA_ker k).mp hk)
      rw [sup_eq_left.mpr hker_le, top_sup_eq]
      rw [← Subgroup.subgroupOf_self L]
      exact Subgroup.relIndex_subgroupOf le_rfl
    rw [hrel]
    exact hSodd
  have hS'norm : L' ⊓ Subgroup.normalizer (S' : Set ↥α.range) ≤ P' := by
    intro y hy
    obtain ⟨hyL', hyN⟩ := Subgroup.mem_inf.mp hy
    rw [← hA_range] at hyL'
    obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp hyL'
    rw [← hl]
    have hlN : (l : G) ∈ Subgroup.normalizer (S : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      apply Subgroup.eq_of_le_of_card_ge
      · intro x hx
        obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
        change ((l * ⟨s, hSL hs⟩ * l⁻¹ : ↥L) : G) ∈ S
        have hs₀ : (⟨s, hSL hs⟩ : ↥L) ∈ S₁ := by rw [Subgroup.mem_subgroupOf]; exact hs
        have hAS : A ⟨s, hSL hs⟩ ∈ S' := Subgroup.mem_map_of_mem A hs₀
        have hyconj : y * A ⟨s, hSL hs⟩ * y⁻¹ ∈ S' :=
          (Subgroup.mem_normalizer_iff.mp hyN (A ⟨s, hSL hs⟩)).mp hAS
        have hprod : A (l * ⟨s, hSL hs⟩ * l⁻¹) ∈ S' := by
          rw [show A (l * ⟨s, hSL hs⟩ * l⁻¹) = A l * A ⟨s, hSL hs⟩ * (A l)⁻¹ by
            rw [map_mul, map_mul, map_inv]]
          rw [hl]
          exact hyconj
        obtain ⟨s₁, hs₁, hs₁eq⟩ := Subgroup.mem_map.mp hprod
        have hker : ((s₁⁻¹ * (l * ⟨s, hSL hs⟩ * l⁻¹) : ↥L) : G) ∈ K := by
          apply (hA_ker _).mp
          rw [map_mul, map_inv, hs₁eq, inv_mul_cancel]
        have hval : ((l * ⟨s, hSL hs⟩ * l⁻¹ : ↥L) : G) =
            (s₁ : G) * ((s₁⁻¹ * (l * ⟨s, hSL hs⟩ * l⁻¹) : ↥L) : G) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [hval]
        exact S.mul_mem (Subgroup.mem_subgroupOf.mp hs₁) (hKS hker)
      · exact le_of_eq (Subgroup.card_map_of_injective
          (f := (MulAut.conj (l : G)).toMonoidHom)
          (fun a b h => (MulAut.conj (l : G)).injective h)).symm
    have hlP : (l : G) ∈ P := hSnorm (Subgroup.mem_inf.mpr ⟨l.2, hlN⟩)
    exact Subgroup.mem_map_of_mem A (by rw [Subgroup.mem_subgroupOf]; exact hlP)
  refine ⟨hτN, ⟨P', ⟨bot_le, hP'lt, hP'max, S', bot_le, hS'le, hS'pow, hS'odd, hS'norm⟩, ?_⟩⟩
  intro y hy
  rw [← hA_range] at hy
  obtain ⟨l₀, hl₀⟩ := MonoidHom.mem_range.mp hy
  rw [← hl₀]
  intro heq
  have hnorm : τ⁻¹ * A l₀ ∈ Subgroup.normalizer (P' : Set ↥α.range) :=
    conjSubgroup_eq_iff_mem_normalizer.mp heq
  have hPle : P ≤ conjSubgroup P (t⁻¹ * (l₀ : G)) := by
    intro p hp
    rw [mem_conjSubgroup_iff]
    have hp₁ : (⟨p, hPLt.le hp⟩ : ↥L) ∈ P₁ := by
      rw [Subgroup.mem_subgroupOf]; exact hp
    have hApP' : A ⟨p, hPLt.le hp⟩ ∈ P' := Subgroup.mem_map_of_mem A hp₁
    have hconjP' : (τ⁻¹ * A l₀) * A ⟨p, hPLt.le hp⟩ * (τ⁻¹ * A l₀)⁻¹ ∈ P' :=
      (Subgroup.mem_normalizer_iff.mp hnorm (A ⟨p, hPLt.le hp⟩)).mp hApP'
    let q : ↥L := ⟨(l₀ : G) * p * (l₀ : G)⁻¹,
      L.mul_mem (L.mul_mem l₀.2 (hPLt.le hp)) (L.inv_mem l₀.2)⟩
    have hq_eq : q = l₀ * ⟨p, hPLt.le hp⟩ * l₀⁻¹ := by ext; rfl
    let gpg : ↥L := ⟨t⁻¹ * (q : G) * t,
      (Subgroup.mem_set_normalizer_iff''.mp htN (q : G)).mp q.2⟩
    have hAgpg : A gpg = (τ⁻¹ * A l₀) * A ⟨p, hPLt.le hp⟩ * (τ⁻¹ * A l₀)⁻¹ := by
      rw [show A gpg = τ⁻¹ * A q * τ from hτ_conj_inv q]
      rw [hq_eq, map_mul, map_mul, map_inv]
      group
    have hAgpgP' : A gpg ∈ P' := by rw [hAgpg]; exact hconjP'
    obtain ⟨p', hp', hp'eq⟩ := Subgroup.mem_map.mp hAgpgP'
    have hker : ((p'⁻¹ * gpg : ↥L) : G) ∈ K := by
      apply (hA_ker _).mp
      rw [map_mul, map_inv, hp'eq, inv_mul_cancel]
    have hval : (gpg : G) = (p' : G) * ((p'⁻¹ * gpg : ↥L) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hgpgval : (gpg : G) = (t⁻¹ * (l₀ : G)) * p * (t⁻¹ * (l₀ : G))⁻¹ := by
      simp only [gpg, q, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [← hgpgval, hval]
    exact P.mul_mem hp' (hKP hker)
  refine hconj (l₀ : G) l₀.2 ?_
  have hcard : Nat.card (conjSubgroup P (t⁻¹ * (l₀ : G))) ≤ Nat.card P :=
    le_of_eq (Subgroup.card_map_of_injective
      (MulAut.conj (t⁻¹ * (l₀ : G))⁻¹).injective)
  exact (Subgroup.eq_of_le_of_card_ge hPle hcard).symm

end CFSG.LocalAnalysis.WeakClosure81

end
