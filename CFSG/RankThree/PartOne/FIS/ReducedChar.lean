module

public import CFSG.RankThree.PartOne.FIS.SymBuild
public import CFSG.RankThree.PartOne.FIS.LocalTransport
public import CFSG.RankThree.PartOne.FIS.AutTop

public section

namespace CFSG.RankThree.PartOne.FIS

open CFSG.RankThree.PartTwo.Sec7 (conjOrbit)
open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification Equiv Equiv.Perm

theorem star_subset_conjOrbit {X : Type} [Group X] {E : Set X} (hP : Pair X E)
    (hZ : Subgroup.center X = ⊥) {N : Subgroup X} (hNn : N.Normal) (hNs : IsSimpleGroup N)
    (hNbot : N ≠ ⊥) {e x : X} (he : e ∈ E) (hx : x ∈ LocalClass E e) :
    ∃ m ∈ N, x = m * e * m⁻¹ := by
  have h1 := mk_eq_of_comm_of_normal hP hZ hNn hNs hNbot he hx.1 hx.2.2.symm
  rw [Pair.inv_eq hP he] at h1
  have hxe : x * e ∈ N := by rw [hx.2.2]; exact h1
  exact exists_conj_of_mul_mem hP hZ hNn he hx.1 hxe

theorem exists_commuting_pair {X : Type} [Group X] {E : Set X} {d : X} {n : ℕ} (h4 : 4 ≤ n)
    (L : LocalIso E d n) :
    ∃ e ∈ LocalClass E d, ∃ e' ∈ LocalClass E d, e ≠ e' ∧ e * e' = e' * e := by
  obtain ⟨a, b, c, e, hab, hce, hac, hae, hbc, hbe⟩ : ∃ a b c e : Fin n, a ≠ b ∧ c ≠ e ∧
      a ≠ c ∧ a ≠ e ∧ b ≠ c ∧ b ≠ e :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩, by simp [Fin.ext_iff],
      by simp [Fin.ext_iff], by simp [Fin.ext_iff], by simp [Fin.ext_iff], by simp [Fin.ext_iff],
      by simp [Fin.ext_iff]⟩
  have h1 : (swap a b).IsSwap := ⟨a, b, hab, rfl⟩
  have h2 : (swap c e).IsSwap := ⟨c, e, hce, rfl⟩
  have hcomm : swap a b * swap c e = swap c e * swap a b :=
    PermFacts.swap_mul_comm_of_disjoint hac hae hbc hbe
  refine ⟨_, L.mem_of_swap h1, _, L.mem_of_swap h2, ?_, ?_⟩
  · intro h
    have h' := L.φ.symm.injective (Subtype.ext h)
    have h'' := congrArg (fun f : Perm (Fin n) => f a) h'
    simp only [swap_apply_left] at h''
    rw [swap_apply_of_ne_of_ne hac hae] at h''
    exact hab h''.symm
  · have hc : L.φ.symm (swap a b) * L.φ.symm (swap c e) =
        L.φ.symm (swap c e) * L.φ.symm (swap a b) := by
      rw [← map_mul, ← map_mul, hcomm]
    exact congrArg Subtype.val hc

theorem subset_conjOrbit_of_four {X : Type} [Group X] {E : Set X} (hP : Pair X E)
    (hZ : Subgroup.center X = ⊥) {N : Subgroup X} (hNn : N.Normal) (hNs : IsSimpleGroup N)
    (hNbot : N ≠ ⊥) {n : ℕ} (hI : PermInput n) (h4 : 4 ≤ n) {d : X} (hd : d ∈ E)
    (L : LocalIso E d n) : E ⊆ conjOrbit N d := by
  intro x hx
  by_contra hxS
  have hclosed : ∀ e ∈ conjOrbit N d, ∀ y ∈ E, y * e = e * y → y ∈ conjOrbit N d := by
    rintro _ ⟨m, hm, rfl⟩ y hy hcomm
    by_cases hye : y = m * d * m⁻¹
    · exact ⟨m, hm, hye⟩
    · obtain ⟨m', hm', hy'⟩ := star_subset_conjOrbit hP hZ hNn hNs hNbot
        (Pair.conj_mem hP hd m) (x := y) ⟨hy, hye, hcomm⟩
      exact ⟨m' * m, mul_mem hm' hm, by rw [hy']; group⟩
  have hxd : x * d ≠ d * x := fun h => hxS (hclosed d ⟨1, one_mem _, by simp⟩ x hx h)
  have hxe : ∀ e ∈ LocalClass E d, x * e ≠ e * x := by
    intro e he h
    obtain ⟨m, hm, hme⟩ := star_subset_conjOrbit hP hZ hNn hNs hNbot hd he
    exact hxS (hclosed e ⟨m, hm, hme⟩ x hx h)
  obtain ⟨e, he, e', he', hne, hcomm⟩ := exists_commuting_pair h4 L
  obtain ⟨y₁, h1, y₂, h2, y₃, h3, h12, h13, h23, c12, c13, c23⟩ :=
    w4 hP hx hd he.1 he'.1 he.2.2.symm he'.2.2.symm hcomm he.2.1.symm he'.2.1.symm hne hxd
      (hxe e he) (hxe e' he')
  exact no_three_at hI hP hd L hx h1 h2 h3 h12 h13 h23 c12 c13 c23

theorem nonempty_localIso_Kgrp {X : Type} [Group X] {E : Set X} (hP : Pair X E)
    (hZ : Subgroup.center X = ⊥) {N : Subgroup X} (hNn : N.Normal) (hNs : IsSimpleGroup N)
    (hNbot : N ≠ ⊥) {d : X} (hd : d ∈ E) {n : ℕ} (L : LocalIso E d n) :
    Nonempty (LocalIso (Subtype.val ⁻¹' conjOrbit N d : Set ↥(Kgrp N d))
      ⟨d, mem_Kgrp_self N d⟩ n) := by
  obtain ⟨ι, -, hι⟩ := exists_localEquiv (E := (Subtype.val ⁻¹' conjOrbit N d : Set ↥(Kgrp N d)))
    (F := E) (d := (⟨d, mem_Kgrp_self N d⟩ : ↥(Kgrp N d))) (Kgrp N d).subtype
    (fun a _ b _ h => Subtype.ext h)
    (fun x hx => ⟨conjOrbit_subset hP hd hx.1, fun h => hx.2.1 (Subtype.ext h),
      congrArg Subtype.val hx.2.2⟩)
    (fun y hy => by
      obtain ⟨m, hm, hym⟩ := star_subset_conjOrbit hP hZ hNn hNs hNbot hd hy
      have hyK : y ∈ Kgrp N d := conjOrbit_subset_Kgrp N d ⟨m, hm, hym⟩
      exact ⟨⟨y, hyK⟩, ⟨⟨m, hm, hym⟩, fun h => hy.2.1 (congrArg Subtype.val h),
        Subtype.ext hy.2.2⟩, rfl⟩)
  exact ⟨L.transportSymm ι hι⟩

theorem Kgrp_eq_top_of_three {H : Type} [Group H] [Finite H] {E : Set H} (hP : Pair H E)
    (hZ : Subgroup.center H = ⊥) {N : Subgroup H} (hNn : N.Normal) (hNs : IsSimpleGroup N)
    (hNsol : ¬ Group.IsSolvable N) (hNbot : N ≠ ⊥) {d : H} (hd : d ∈ E)
    (hcent : Subgroup.centralizer (N : Set H) = ⊥)
    (Ψ : Perm (Fin 5) ≃* ↥(Kgrp N d)) : Kgrp N d = ⊤ := by
  have := hNn
  let g : Perm (Fin 5) →* H := (Kgrp N d).subtype.comp Ψ.toMonoidHom
  have hginj : Function.Injective g := (Subgroup.subtype_injective _).comp Ψ.injective
  have hgrange : g.range = Kgrp N d := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 Ψ.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  have hmap : (alternatingGroup (Fin 5)).map g = N := by
    rw [← alternatingGroup.commutator_perm_eq (by simp), commutator_def,
      Subgroup.map_commutator, Subgroup.map_top, hgrange]
    exact commutator_Kgrp hP hZ hNn hNs hNsol hNbot hd
  let e : N ≃* alternatingGroup (Fin 5) :=
    ((Subgroup.equivMapOfInjective _ g hginj).trans (MulEquiv.subgroupCongr hmap)).symm
  exact eq_top_of_normal_alternating N (Kgrp N d) hcent 5 le_rfl (by norm_num) e
    (Nat.card_congr Ψ.toEquiv).le

theorem reduced_char {H : Type} [Group H] {E : Set H} (hP : Pair H E)
    (hZ : Subgroup.center H = ⊥) (h2 : ∀ N : Subgroup H, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup H, N.Normal → IsPGroup 3 N → N = ⊥) {n : ℕ} (hI : PermInput n)
    (hn3 : 3 ≤ n) {d : H} (hd : d ∈ E) (L : LocalIso E d n) :
    ∃ Ψ : Perm (Fin (n + 2)) ≃* H, Ψ '' {σ | σ.IsSwap} = E := by
  have := Pair.finite hP
  have htop : (⊤ : Subgroup H) ≠ ⊥ := by
    intro h
    have := Subgroup.mem_top d
    rw [h, Subgroup.mem_bot] at this
    exact Pair.ne_one hP hd this
  obtain ⟨N, hNn, -, hNbot, hmin⟩ := CFSG.exists_minimal_normal_le ⊤ inferInstance htop
  have hNs := Pair.isSimpleGroup_of_minimal hP hZ h2 h3 hNn hNbot hmin
  have hNsol := Pair.not_isSolvable_of_minimal hP hZ h2 h3 hNn hNbot hmin
  have hcent := centralizer_eq_bot_of_minimal hP hZ h2 h3 hNn hNbot hmin
  have hPK := pair_Kgrp hP hZ hNn hNs hNbot hd
  have hZK := center_Kgrp hP hZ hNn hNs hNbot hd hcent
  obtain ⟨hSK, hnaK⟩ := isSimpleGroup_commutator_Kgrp hP hZ hNn hNs hNsol hNbot hd
  have hdK : d ∈ Kgrp N d := mem_Kgrp_self N d
  have hdE : (⟨d, hdK⟩ : ↥(Kgrp N d)) ∈ (Subtype.val ⁻¹' conjOrbit N d : Set ↥(Kgrp N d)) :=
    ⟨1, one_mem _, by simp⟩
  obtain ⟨LK⟩ := nonempty_localIso_Kgrp hP hZ hNn hNs hNbot hd L
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨ΨK, hΨK⟩ := symmetric_char hI (by omega) hPK hZK hSK hnaK hdE LK
  have hKtop : Kgrp N d = ⊤ := by
    by_cases hm : 3 ≤ m
    · have hsub := subset_conjOrbit_of_four hP hZ hNn hNs hNbot hI (by omega) hd L
      rw [eq_top_iff, ← Pair.closure_eq hP, Subgroup.closure_le]
      exact fun x hx => conjOrbit_subset_Kgrp N d (hsub hx)
    · obtain rfl : m = 2 := by omega
      exact Kgrp_eq_top_of_three hP hZ hNn hNs hNsol hNbot hd hcent ΨK
  have hEsub : E ⊆ conjOrbit N d := by
    intro x hx
    obtain ⟨g, hg⟩ := isConj_iff.1 (Pair.isConj hP hd hx)
    have hgK : g ∈ Kgrp N d := by rw [hKtop]; trivial
    have hxK : x ∈ Kgrp N d := by
      rw [← hg]
      exact mul_mem (mul_mem hgK hdK) (inv_mem hgK)
    have hxE : (⟨x, hxK⟩ : ↥(Kgrp N d)) ∈ (Subtype.val ⁻¹' conjOrbit N d : Set ↥(Kgrp N d)) := by
      refine Pair.mem_of_isConj hPK hdE (isConj_iff.2 ⟨⟨g, hgK⟩, Subtype.ext ?_⟩)
      simpa using hg
    exact hxE
  let eK : ↥(Kgrp N d) ≃* H := (MulEquiv.subgroupCongr hKtop).trans Subgroup.topEquiv
  have heK : ∀ x : ↥(Kgrp N d), eK x = (x : H) := fun x => rfl
  refine ⟨ΨK.trans eK, ?_⟩
  ext x
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    have hmem : ΨK σ ∈ (Subtype.val ⁻¹' conjOrbit N d : Set ↥(Kgrp N d)) := by
      rw [← hΨK]
      exact ⟨σ, hσ, rfl⟩
    exact conjOrbit_subset hP hd hmem
  · intro hx
    have hxS := hEsub hx
    have hxK : x ∈ Kgrp N d := conjOrbit_subset_Kgrp N d hxS
    have hmem : (⟨x, hxK⟩ : ↥(Kgrp N d)) ∈ (Subtype.val ⁻¹' conjOrbit N d : Set ↥(Kgrp N d)) :=
      hxS
    rw [← hΨK] at hmem
    obtain ⟨σ, hσ, hσx⟩ := hmem
    exact ⟨σ, hσ, by rw [MulEquiv.trans_apply, heK, hσx]⟩

end CFSG.RankThree.PartOne.FIS
