module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreOffender

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def cj (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

theorem mem_cj {g x : G} {H : Subgroup G} : x ∈ cj g H ↔ g⁻¹ * x * g ∈ H := by
  unfold cj
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem cj_cj (g h : G) (H : Subgroup G) : cj g (cj h H) = cj (g * h) H := by
  ext x
  simp only [mem_cj, mul_inv_rev, mul_assoc]

theorem cj_one (H : Subgroup G) : cj 1 H = H := by
  ext x
  simp [mem_cj]

theorem cj_mono (g : G) {H K : Subgroup G} (h : H ≤ K) : cj g H ≤ cj g K :=
  Subgroup.map_mono h

theorem cj_eq_of_mem_normalizer {g : G} {H : Subgroup G} (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    cj g H = H :=
  CFSG.Quasithin.map_conj_eq_of_mem_normalizer hg

theorem cj_mul_of_mem_normalizer {a s : G} {H : Subgroup G}
    (hs : s ∈ Subgroup.normalizer (H : Set G)) : cj (a * s) H = cj a H := by
  rw [← cj_cj, cj_eq_of_mem_normalizer hs]

theorem cj_le_of_mem {g : G} {H K : Subgroup G} (hg : g ∈ K) (hH : H ≤ K) : cj g H ≤ K := by
  intro x hx
  rw [mem_cj] at hx
  have := K.mul_mem (K.mul_mem hg (hH hx)) (K.inv_mem hg)
  simpa [mul_assoc] using this

theorem cj_le_of_le_of_mem_normalizer {g : G} {H K : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hH : H ≤ K) : cj g H ≤ K := by
  intro x hx
  rw [mem_cj] at hx
  have := (Subgroup.mem_normalizer_iff.mp hg _).mp (hH hx)
  simpa [mul_assoc] using this

@[expose] def conjJoin (X J : Subgroup G) : Subgroup G := ⨆ g ∈ X, cj g J

theorem cj_le_conjJoin {X J : Subgroup G} {g : G} (hg : g ∈ X) : cj g J ≤ conjJoin X J :=
  le_iSup₂_of_le g hg le_rfl

theorem le_conjJoin {X J : Subgroup G} : J ≤ conjJoin X J := by
  have := cj_le_conjJoin (J := J) X.one_mem
  rwa [cj_one] at this

theorem conjJoin_le {X J K : Subgroup G} (h : ∀ g ∈ X, cj g J ≤ K) : conjJoin X J ≤ K :=
  iSup₂_le h

theorem conjJoin_le_of_le {X J K : Subgroup G} (hJK : J ≤ K)
    (hKn : X ≤ Subgroup.normalizer (K : Set G)) : conjJoin X J ≤ K :=
  conjJoin_le fun _ hg => cj_le_of_le_of_mem_normalizer (hKn hg) hJK

theorem cj_conjJoin_le {X J : Subgroup G} {g : G} (hg : g ∈ X) :
    cj g (conjJoin X J) ≤ conjJoin X J := by
  show cj g (conjJoin X J) ≤ _
  unfold conjJoin
  rw [cj, Subgroup.map_iSup]
  refine iSup_le fun h => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hh => ?_
  have := cj_le_conjJoin (J := J) (X.mul_mem hg hh)
  rw [← cj_cj] at this
  exact this

theorem le_normalizer_conjJoin (X J : Subgroup G) :
    X ≤ Subgroup.normalizer (conjJoin X J : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : g * x * g⁻¹ ∈ cj g (conjJoin X J) := by
      rw [mem_cj]; simpa [mul_assoc] using hx
    exact cj_conjJoin_le hg this
  · intro hx
    have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ cj g⁻¹ (conjJoin X J) := by
      rw [mem_cj]; simpa [mul_assoc] using hx
    have := cj_conjJoin_le (X.inv_mem hg) h2
    simpa [mul_assoc] using this

section T4

variable {X S Z : Subgroup G}

theorem le_normalizer_thompsonJ_of_le {S T : Subgroup G} (hT : T ≤ S) :
    T ≤ Subgroup.normalizer (thompsonJ S : Set G) :=
  hT.trans (Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ S))

theorem pow_mul_mem {I K : Subgroup G} (hK : K ≤ Subgroup.normalizer (I : Set G)) {i s : G}
    (hi : i ∈ I) (hs : s ∈ K) (n : ℕ) : ∃ i' ∈ I, (i * s) ^ n = i' * s ^ n := by
  induction n with
  | zero => exact ⟨1, I.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨i', hi', h⟩ := ih
    refine ⟨i' * (s ^ n * i * (s ^ n)⁻¹), I.mul_mem hi' ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hK (K.pow_mem hs n)) i).mp hi
    · rw [pow_succ, h]; group

theorem conjJoin_eq_sup_cj [Finite G] (h : PushHyp X S Z) {g₀ : G} (hg₀ : g₀ ∈ pResidualOf 2 X)
    (hgen : pResidualOf 2 X ≤ (thompsonJ S ⊔ cj g₀ (thompsonJ S)) ⊔ pCoreOf 2 X) :
    conjJoin X (thompsonJ S) = thompsonJ S ⊔ cj g₀ (thompsonJ S) ∧
      pResidualOf 2 X ≤ conjJoin X (thompsonJ S) := by
  set J := thompsonJ S with hJ
  set L := pResidualOf 2 X with hL
  set Q := pCoreOf 2 X with hQ
  set I₂ := J ⊔ cj g₀ J with hI₂
  have hJS : J ≤ S := thompsonJ_le_self S
  have hSJ : S ≤ Subgroup.normalizer (J : Set G) := le_normalizer_thompsonJ_of_le le_rfl
  have hLX : L ≤ X := pResidualOf_le_self X
  have hXLS : L ⊔ S = X := pResidualOf_sup_eq_of_sylow h.sylow
  have hSX : S ≤ X := h.le_self
  have hJX : J ≤ X := hJS.trans hSX
  have hg₀X : g₀ ∈ X := hLX hg₀
  have hI₂X : I₂ ≤ X := sup_le hJX (cj_le_of_mem hg₀X hJX)
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hI₂le : conjJoin X J ≤ I₂ := by
    refine conjJoin_le fun g hg => ?_
    rw [← hXLS] at hg
    obtain ⟨l, hl, s, hs, rfl⟩ := mem_sup_of_le_normalizer (hSX.trans (le_normalizer_pResidualOf X)) hg
    have hl' : l ∈ Q ⊔ I₂ := by rw [sup_comm]; exact hgen hl
    obtain ⟨q, hq, i, hi, rfl⟩ := mem_sup_of_le_normalizer (hI₂X.trans hXQ) hl'
    have hq' : i⁻¹ * q * i ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (hXQ (hI₂X (I₂.inv_mem hi))) q).mp hq
      simpa using this
    have hqS : (i⁻¹ * q * i) * s ∈ S := S.mul_mem (h.core_le hq') hs
    have e : q * i * s = i * ((i⁻¹ * q * i) * s) := by group
    rw [e, cj_mul_of_mem_normalizer (hSJ hqS)]
    exact cj_le_of_mem hi (le_sup_left)
  have hI₂ge : I₂ ≤ conjJoin X J :=
    sup_le le_conjJoin (cj_le_conjJoin hg₀X)
  refine ⟨le_antisymm hI₂le hI₂ge, ?_⟩
  set I := conjJoin X J with hI
  have hIn : X ≤ Subgroup.normalizer (I : Set G) := le_normalizer_conjJoin X J
  have hLI : L ≤ I ⊔ S := by
    refine hgen.trans (sup_le ?_ (h.core_le.trans le_sup_right))
    exact (le_antisymm hI₂le hI₂ge ▸ le_sup_left)
  have hXI : X ≤ I ⊔ S := by rw [← hXLS]; exact sup_le hLI le_sup_right
  rw [hL, ← oTwoUpper_eq_pResidualOf]
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  obtain ⟨i, hi, s, hs, rfl⟩ := mem_sup_of_le_normalizer (hSX.trans hIn) (hXI hx)
  obtain ⟨k, hk⟩ := h.sylow.2.1 ⟨s, hs⟩
  have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨i', hi', he⟩ := pow_mul_mem (hSX.trans hIn) hi hs (2 ^ k)
  exact ⟨k, by rw [he, hk', mul_one]; exact hi'⟩

end T4

section T5

theorem centralizer_sup_eq (A B : Subgroup G) :
    Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le (by exact_mod_cast le_sup_left))
      (Subgroup.centralizer_le (by exact_mod_cast le_sup_right))
  · intro x ⟨hxA, hxB⟩
    have hle : A ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
        exact (Subgroup.mem_centralizer_iff.mp hxA a ha).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
        exact (Subgroup.mem_centralizer_iff.mp hxB b hb).symm
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := Subgroup.mem_centralizer_iff.mp (hle hy) x rfl
    exact this.symm

theorem cj_inf_centralizer {g : G} {M J : Subgroup G} (hg : g ∈ Subgroup.normalizer (M : Set G)) :
    cj g (M ⊓ Subgroup.centralizer (J : Set G)) = M ⊓ Subgroup.centralizer (cj g J : Set G) := by
  unfold cj
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    CFSG.Quasithin.centralizer_map_mulEquiv, CFSG.Quasithin.map_conj_eq_of_mem_normalizer hg]

theorem relIndex_inf_centralizer_sup_cj_le {g : G} {M J : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (M : Set G)) :
    (M ⊓ Subgroup.centralizer ((J ⊔ cj g J : Subgroup G) : Set G)).relIndex M ≤
      ((M ⊓ Subgroup.centralizer (J : Set G)).relIndex M) ^ 2 := by
  have h1 : M ⊓ Subgroup.centralizer ((J ⊔ cj g J : Subgroup G) : Set G) =
      (M ⊓ Subgroup.centralizer (J : Set G)) ⊓ (M ⊓ Subgroup.centralizer (cj g J : Set G)) := by
    rw [centralizer_sup_eq]; ext x; simp only [Subgroup.mem_inf]; tauto
  have h2 : (M ⊓ Subgroup.centralizer (cj g J : Set G)).relIndex M =
      (M ⊓ Subgroup.centralizer (J : Set G)).relIndex M := by
    rw [← cj_inf_centralizer hg]
    have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (M ⊓ Subgroup.centralizer (J : Set G)) M (MulAut.conj g).injective
    rw [CFSG.Quasithin.map_conj_eq_of_mem_normalizer hg] at this
    exact this
  rw [h1, pow_two]
  refine Subgroup.relIndex_inf_le.trans ?_
  rw [h2]

theorem relIndex_sup_centralizer {Z M D : Subgroup G} (hZM : Z ≤ M) (hDM : D ≤ M)
    (hDZ : D ≤ Subgroup.normalizer (Z : Set G)) [Finite G] :
    D.relIndex M = (Z ⊓ D).relIndex Z * (Z ⊔ D).relIndex M := by
  have h1 : D.relIndex (Z ⊔ D) = (Z ⊓ D).relIndex Z := relIndex_sup_eq_relIndex_inf hDZ
  rw [← h1]
  exact (Subgroup.relIndex_mul_relIndex D (Z ⊔ D) M le_sup_right (sup_le hZM hDM)).symm

end T5

end CFSG.Quasithin.F53Push
