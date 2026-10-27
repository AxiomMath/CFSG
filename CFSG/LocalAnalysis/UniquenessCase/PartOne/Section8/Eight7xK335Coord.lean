module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open scoped Pointwise

private instance k335crd_factPrimeThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩


@[expose] def K335Coord (X : Type) [Group X] (a : ℕ) : Prop :=
  ∃ (C : Type) (_ : CommGroup C) (_ : Finite C), Nat.card C = 3 ^ a ∧
    ∃ φ : (Fin 3 → C) →* X, Function.Injective φ ∧ ∃ s : X, s ^ 3 = 1 ∧
      (∀ x : Fin 3 → C, s * φ x * s⁻¹ = φ (fun i => x (i - 1))) ∧
      ∀ c : C, c ^ 3 = 1 → c ≠ 1 → ∃ g : X, ∃ u : Fin 3 → C,
        (∀ i, u i ∈ Subgroup.zpowers c) ∧ u 0 * u 1 * u 2 ≠ 1 ∧ g * φ (fun _ => c) * g⁻¹ = φ u

theorem K335Coord.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {a : ℕ}
    (h : K335Coord X a) : K335Coord Y a := by
  obtain ⟨C, _, _, hC, φ, hφ, s, hs3, hs, hmove⟩ := h
  refine ⟨C, inferInstance, inferInstance, hC, e.toMonoidHom.comp φ, e.injective.comp hφ, e s,
    by rw [← map_pow, hs3, map_one], fun x => ?_, fun c hc3 hc1 => ?_⟩
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_inv, ← map_mul, ← map_mul, hs]
  · obtain ⟨g, u, hu, hu1, hg⟩ := hmove c hc3 hc1
    refine ⟨e g, u, hu, hu1, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_inv, ← map_mul, ← map_mul, hg]

theorem K335Coord.map {X Y : Type} [Group X] [Group Y] (ψ : X →* Y)
    (hψ : ¬ 3 ∣ Nat.card ψ.ker) {a : ℕ} (h : K335Coord X a) : K335Coord Y a := by
  obtain ⟨C, _, _, hC, φ, hφ, s, hs3, hs, hmove⟩ := h
  have hinj : Function.Injective (ψ.comp φ) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hcop : Nat.Coprime (3 ^ a) (Nat.card ψ.ker) :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hψ).pow_left a
    have hxC : x ^ 3 ^ a = 1 := funext fun i => by
      rw [Pi.pow_apply, ← hC, pow_card_eq_one', Pi.one_apply]
    have h1 : φ x ^ 3 ^ a = 1 := by rw [← map_pow, hxC, map_one]
    have h2 : φ x ^ Nat.card ψ.ker = 1 := by
      have := pow_card_eq_one' (G := ψ.ker) (x := ⟨φ x, MonoidHom.mem_ker.2 hx⟩)
      simpa using congrArg Subtype.val this
    have h3 : φ x = 1 := by
      have := pow_gcd_eq_one.2 ⟨h1, h2⟩
      rwa [hcop.gcd_eq_one, pow_one] at this
    exact hφ (h3.trans (map_one φ).symm)
  refine ⟨C, inferInstance, inferInstance, hC, ψ.comp φ, hinj, ψ s,
    by rw [← map_pow, hs3, map_one], fun x => ?_, fun c hc3 hc1 => ?_⟩
  · simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, hs]
  · obtain ⟨g, u, hu, hu1, hg⟩ := hmove c hc3 hc1
    refine ⟨ψ g, u, hu, hu1, ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, hg]

private lemma k335crd_exists_order_three (C : Type) [CommGroup C] [Finite C] {a : ℕ}
    (ha : 1 ≤ a) (hC : Nat.card C = 3 ^ a) : ∃ c : C, c ^ 3 = 1 ∧ c ≠ 1 := by
  have hdvd : 3 ∣ Nat.card C := by
    rw [hC]; exact dvd_pow_self 3 (by omega)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  exact ⟨c, by rw [← hc]; exact pow_orderOf_eq_one c, by rintro rfl; simp at hc⟩

private lemma k335crd_s_not_mem_range (C X : Type) [CommGroup C] [Finite C] [Group X]
    {a : ℕ} (ha : 1 ≤ a) (hC : Nat.card C = 3 ^ a) {φ : (Fin 3 → C) →* X}
    (hφ : Function.Injective φ) {s : X} (hs : ∀ x : Fin 3 → C,
      s * φ x * s⁻¹ = φ (fun i => x (i - 1))) : s ∉ φ.range := by
  intro hsR
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hsR
  obtain ⟨c, hc3, hc1⟩ := k335crd_exists_order_three C ha hC
  let x : Fin 3 → C := Pi.mulSingle 0 c
  have hconv : φ (fun i => x (i - 1)) = φ x := by
    rw [← hs x, ← hy, ← map_mul, ← map_inv, ← map_mul]
    congr 1
    funext i
    simp only [Pi.mul_apply, Pi.inv_apply]
    simp [mul_comm]
  have hx : (fun i : Fin 3 => x (i - 1)) = x := hφ hconv
  have h1 := congrFun hx 1
  simp [x] at h1
  exact hc1 h1

private lemma k335crd_card_pi (C : Type) [CommGroup C] [Finite C] (a : ℕ)
    (hC : Nat.card C = 3 ^ a) : Nat.card (Fin 3 → C) = 3 ^ (3 * a) := by
  rw [Nat.card_pi]
  simp_rw [hC]
  simp [pow_succ]
  ring_nf

private lemma k335crd_disjoint_zpowers {X : Type} [Group X] [Finite X] {R : Subgroup X} {s : X}
    (hsR : s ∉ R) (hs3 : s ^ 3 = 1) : Disjoint R (Subgroup.zpowers s) := by
  have hne : s ≠ 1 := by rintro rfl; exact hsR (by simp)
  have hord : orderOf s = 3 := orderOf_eq_prime hs3 hne
  rw [disjoint_iff_inf_le]
  intro z hz
  rw [Subgroup.mem_bot]
  by_contra hz1
  let H : Subgroup ↥(Subgroup.zpowers s) :=
    (R ⊓ Subgroup.zpowers s).subgroupOf (Subgroup.zpowers s)
  have hdiv : Nat.card H ∣ 3 := by
    have := Subgroup.card_subgroup_dvd_card H
    rwa [Nat.card_zpowers, hord] at this
  rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h1 | h3
  · have hHbot : H = ⊥ := (Subgroup.eq_bot_iff_card H).mpr h1
    have hmem : (⟨z, hz.2⟩ : ↥(Subgroup.zpowers s)) ∈ H := by
      rw [show H = (R ⊓ Subgroup.zpowers s).subgroupOf (Subgroup.zpowers s) from rfl,
        Subgroup.mem_subgroupOf]
      exact ⟨hz.1, hz.2⟩
    rw [hHbot] at hmem
    exact hz1 (Subtype.ext_iff.mp (Subgroup.mem_bot.mp hmem))
  · have hsfin : Finite ↥(Subgroup.zpowers s) := Subtype.finite
    have hHfin : Finite ↥H :=
      @Subtype.finite ↥(Subgroup.zpowers s) hsfin (fun x => x ∈ H)
    have hHtop : H = ⊤ :=
      @Subgroup.eq_top_of_card_eq ↥(Subgroup.zpowers s) _ H hHfin
        (by rw [h3, Nat.card_zpowers, hord])
    have hmem : (⟨s, Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one s⟩⟩ :
        ↥(Subgroup.zpowers s)) ∈ H := by
      rw [hHtop]; exact Subgroup.mem_top _
    rw [show H = (R ⊓ Subgroup.zpowers s).subgroupOf (Subgroup.zpowers s) from rfl,
      Subgroup.mem_subgroupOf] at hmem
    exact hsR hmem.1

private lemma k335crd_norm_zpowers {X : Type} [Finite X] [Group X] {C : Type} [CommGroup C]
    {φ : (Fin 3 → C) →* X} {s : X}
    (hs : ∀ x : Fin 3 → C, s * φ x * s⁻¹ = φ (fun i => x (i - 1))) :
    Subgroup.zpowers s ≤ Subgroup.normalizer (φ.range : Set X) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : φ.range.map (MulAut.conj s).toMonoidHom ≤ φ.range := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hr
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hs x]
    exact ⟨_, rfl⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj s).injective]

private lemma k335crd_card_range (C : Type) [CommGroup C] [Finite C] (a : ℕ)
    (hC : Nat.card C = 3 ^ a) {X : Type} [Group X] {φ : (Fin 3 → C) →* X}
    (hφ : Function.Injective φ) : Nat.card φ.range = 3 ^ (3 * a) := by
  rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
  exact k335crd_card_pi C a hC

private lemma k335crd_card_Q {X : Type} [Finite X] [Group X] {C : Type} [CommGroup C] [Finite C]
    {a : ℕ} (ha : 1 ≤ a) (hC : Nat.card C = 3 ^ a) {φ : (Fin 3 → C) →* X}
    (hφ : Function.Injective φ) {s : X} (hs3 : s ^ 3 = 1)
    (hs : ∀ x : Fin 3 → C, s * φ x * s⁻¹ = φ (fun i => x (i - 1))) :
    Nat.card (φ.range ⊔ Subgroup.zpowers s : Subgroup X) = 3 ^ (3 * a + 1) := by
  have hsR : s ∉ φ.range := k335crd_s_not_mem_range C X ha hC hφ hs
  have hord : orderOf s = 3 := orderOf_eq_prime hs3 (by rintro rfl; exact hsR (by simp))
  have hdisj : Disjoint φ.range (Subgroup.zpowers s) := k335crd_disjoint_zpowers hsR hs3
  have hnorm : Subgroup.zpowers s ≤ Subgroup.normalizer (φ.range : Set X) :=
    k335crd_norm_zpowers (C := C) (φ := φ) (s := s) hs
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer φ.range
    (Subgroup.zpowers s) hnorm hdisj
  rw [hcard, k335crd_card_range C a hC hφ, Nat.card_zpowers, hord, ← pow_succ]

private theorem k335crd_center_element {X C : Type} [Group X] [Finite X] [CommGroup C]
    [Finite C] {a : ℕ} (ha : 1 ≤ a) (hC : Nat.card C = 3 ^ a)
    {φ : (Fin 3 → C) →* X} (hφ : Function.Injective φ) {s : X} (hs3 : s ^ 3 = 1)
    (hs : ∀ x : Fin 3 → C, s * φ x * s⁻¹ = φ (fun i => x (i - 1)))
    {P : Subgroup X}
    (hPle : P ≤ φ.range ⊔ Subgroup.zpowers s)
    (hPcard : Nat.card P = 9)
    (hPelem : CFSG.Open.IsElemAbelian 3 P)
    (hPclosed : CFSG.Open.fusionStronglyClosed (P : Set X)
      (φ.range ⊔ Subgroup.zpowers s)) :
    ∃ c : C, c ≠ 1 ∧ c ^ 3 = 1 ∧ φ (fun _ => c) ∈ P := by
  set Q : Subgroup X := φ.range ⊔ Subgroup.zpowers s with hQdef
  have hsR : s ∉ φ.range := k335crd_s_not_mem_range C X ha hC hφ hs
  have hord : orderOf s = 3 := orderOf_eq_prime hs3 (by rintro rfl; exact hsR (by simp))
  have hdisj : Disjoint φ.range (Subgroup.zpowers s) := k335crd_disjoint_zpowers hsR hs3
  have hnorm : Subgroup.zpowers s ≤ Subgroup.normalizer (φ.range : Set X) :=
    k335crd_norm_zpowers (C := C) (φ := φ) (s := s) hs
  have hQmul : (↑Q : Set X) = (φ.range : Set X) * (Subgroup.zpowers s : Set X) := by
    rw [hQdef]
    exact Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm
  have hPleQ : P ≤ Q := hPle
  have hPnormal : (P.subgroupOf Q).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hPleQ]
    intro h k hh hk
    have hmemQ : k * h * k⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hk (hPleQ hh)) (Q.inv_mem hk)
    have := hPclosed h hh (k⁻¹) (by simpa [inv_inv] using hmemQ)
    simpa [inv_inv] using this
  have hHne : P.subgroupOf Q ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (P.subgroupOf Q) = 1 := by rw [hbot]; simp
    have hcard' : Nat.card (P.subgroupOf Q) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleQ)
    rw [hcard', hPcard] at hcard
    norm_num at hcard
  have hQcard : Nat.card Q = 3 ^ (3 * a + 1) := by
    rw [hQdef]
    exact k335crd_card_Q ha hC hφ hs3 hs
  have hQp : IsPGroup 3 Q := IsPGroup.of_card hQcard
  have hcenter : P.subgroupOf Q ⊓ Subgroup.center Q ≠ ⊥ :=
    @Group.IsNilpotent.inf_center_ne_bot_of_normal Q _ (hQp.isNilpotent)
      (P.subgroupOf Q) hPnormal hHne
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcenter
  have hzP : (z : Q) ∈ P.subgroupOf Q := (Subgroup.mem_inf.mp z.2).1
  have hzC : (z : Q) ∈ Subgroup.center Q := (Subgroup.mem_inf.mp z.2).2
  have hzP' : ((z : Q) : X) ∈ P := hzP
  have hz1' : (z : Q) ≠ 1 := by
    intro h
    exact hz1 (Subtype.ext h)
  have hzX1 : ((z : Q) : X) ≠ 1 := by
    intro h
    exact hz1' (Subtype.ext h)
  have hzQmem : ((z : Q) : X) ∈ (Q : Set X) := (z : Q).2
  rw [hQmul] at hzQmem
  obtain ⟨aa, haa, bb, hbb, hab⟩ := hzQmem
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 haa
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hbb
  have hzdecomp : ((z : Q) : X) = φ x * s ^ k := by rw [← hab, ← hx, ← hk]
  have hsQ : s ∈ Q := by
    rw [hQdef]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one s⟩)
  have hcent_s : (⟨s, hsQ⟩ : Q) * z = z * ⟨s, hsQ⟩ :=
    Subgroup.mem_center_iff.mp hzC ⟨s, hsQ⟩
  have hs_comm : s * ((z : Q) : X) = ((z : Q) : X) * s := by
    have := congrArg Subtype.val hcent_s
    simpa using this
  have hcomm_sx : s * φ x = φ x * s := by
    rw [hzdecomp] at hs_comm
    have h2 : s * φ x * s ^ k = φ x * s ^ k * s := by simpa [mul_assoc] using hs_comm
    have hsz : s ^ k * s = s * s ^ k := by
      calc s ^ k * s = s ^ k * s ^ 1 := by simp
        _ = s ^ (k + 1) := (zpow_add s k 1).symm
        _ = s ^ (1 + k) := by rw [add_comm]
        _ = s ^ 1 * s ^ k := zpow_add s 1 k
        _ = s * s ^ k := by simp
    have h2' : s * φ x * s ^ k = φ x * s * s ^ k := by
      calc s * φ x * s ^ k = φ x * s ^ k * s := h2
        _ = φ x * (s ^ k * s) := by rw [mul_assoc]
        _ = φ x * (s * s ^ k) := by rw [hsz]
        _ = φ x * s * s ^ k := by rw [mul_assoc]
    exact mul_right_cancel h2'
  have hsig : (fun i => x (i - 1)) = x := by
    apply hφ
    rw [← hs x, hcomm_sx]
    simp
  have hxconst : x = fun _ => x 0 := by
    funext i
    have h0 := congrFun hsig 1
    have h2 := congrFun hsig 2
    simp at h0 h2
    fin_cases i <;> simp [h0, h2]
  set r : ℤ := k % 3 with hr
  have hsk : s ^ r = s ^ k := by
    have h := zpow_mod_orderOf s k
    rw [hord] at h
    rwa [hr]
  have hr0 : r = 0 := by
    obtain ⟨c1, hc13, hc11⟩ := k335crd_exists_order_three C ha hC
    let m : Fin 3 → C := Pi.mulSingle (0 : Fin 3) c1
    have hphiQ : φ m ∈ Q := by
      rw [hQdef]; exact Subgroup.mem_sup_left ⟨m, rfl⟩
    have hcent_m : (⟨φ m, hphiQ⟩ : Q) * z = z * ⟨φ m, hphiQ⟩ :=
      Subgroup.mem_center_iff.mp hzC ⟨φ m, hphiQ⟩
    have hcomm_m : ((z : Q) : X) * φ m = φ m * ((z : Q) : X) := by
      have := congrArg Subtype.val hcent_m
      simpa using this.symm
    have hrmod : r = 0 ∨ r = 1 ∨ r = 2 := by
      have h0 := Int.emod_nonneg k (by norm_num : (3:ℤ) ≠ 0)
      have hlt := Int.emod_lt_of_pos k (by norm_num : (0:ℤ) < 3)
      omega
    rcases hrmod with h | h | h
    · exact h
    ·
      exfalso
      have hsk1 : s ^ k = s := by rw [← hsk, h, zpow_one]
      rw [hzdecomp, hsk1] at hcomm_m
      have hs1 : s * φ m = φ (fun i => m (i - 1)) * s := by
        calc s * φ m = (s * φ m * s⁻¹) * s := by group
          _ = φ (fun i => m (i - 1)) * s := by rw [hs m]
      have hx1 : (φ x * φ (fun i => m (i - 1))) * s = (φ m * φ x) * s := by
        calc (φ x * φ (fun i => m (i - 1))) * s
            = φ x * (φ (fun i => m (i - 1)) * s) := by rw [mul_assoc]
          _ = φ x * (s * φ m) := by rw [← hs1]
          _ = (φ x * s) * φ m := by rw [mul_assoc]
          _ = φ m * (φ x * s) := hcomm_m
          _ = (φ m * φ x) * s := by rw [mul_assoc]
      have heq : φ x * φ (fun i => m (i - 1)) = φ m * φ x :=
        mul_right_cancel hx1
      rw [hxconst] at heq
      have heq' : (fun _ : Fin 3 => x 0) * (fun i => m (i - 1)) =
          m * (fun _ : Fin 3 => x 0) := by
        apply hφ
        rw [map_mul, map_mul]
        exact heq
      have hpt := congrFun heq' 1
      simp [m, Pi.mulSingle_apply, mul_comm] at hpt
      exact hc11 hpt
    ·
      exfalso
      have hsk2 : s ^ k = s ^ 2 := by
        have h1 : s ^ k = s ^ (2 : ℤ) := by
          rw [← hsk]
          exact congrArg (fun n : ℤ => s ^ n) h
        simpa [mul_comm] using h1
      rw [hzdecomp, hsk2] at hcomm_m
      have hs1 : s * φ m = φ (fun i => m (i - 1)) * s := by
        calc s * φ m = (s * φ m * s⁻¹) * s := by group
          _ = φ (fun i => m (i - 1)) * s := by rw [hs m]
      have hs2 : s * φ (fun i => m (i - 1)) =
          φ (fun i => m (i - 2)) * s := by
        calc s * φ (fun i => m (i - 1))
            = (s * φ (fun i => m (i - 1)) * s⁻¹) * s := by group
          _ = φ (fun i => (fun j => m (j - 1)) (i - 1)) * s := by
              rw [hs (fun i => m (i - 1))]
          _ = φ (fun i => m (i - 2)) * s := by
              congr 2
              funext i
              fin_cases i <;> rfl
      have hss : s ^ 2 * φ m = φ (fun i => m (i - 2)) * s ^ 2 := by
        calc s ^ 2 * φ m = s * (s * φ m) := by rw [pow_two, mul_assoc]
          _ = s * (φ (fun i => m (i - 1)) * s) := by rw [hs1]
          _ = (s * φ (fun i => m (i - 1))) * s := by rw [mul_assoc]
          _ = (φ (fun i => m (i - 2)) * s) * s := by rw [hs2]
          _ = φ (fun i => m (i - 2)) * s ^ 2 := by rw [mul_assoc, pow_two]
      have hx1 : (φ x * φ (fun i => m (i - 2))) * s ^ 2 =
          (φ m * φ x) * s ^ 2 := by
        calc (φ x * φ (fun i => m (i - 2))) * s ^ 2
            = φ x * (φ (fun i => m (i - 2)) * s ^ 2) := by rw [mul_assoc]
          _ = φ x * (s ^ 2 * φ m) := by rw [← hss]
          _ = (φ x * s ^ 2) * φ m := by rw [mul_assoc]
          _ = φ m * (φ x * s ^ 2) := hcomm_m
          _ = (φ m * φ x) * s ^ 2 := by rw [mul_assoc]
      have heq : φ x * φ (fun i => m (i - 2)) = φ m * φ x :=
        mul_right_cancel hx1
      rw [hxconst] at heq
      have heq' : (fun _ : Fin 3 => x 0) * (fun i => m (i - 2)) =
          m * (fun _ : Fin 3 => x 0) := by
        apply hφ
        rw [map_mul, map_mul]
        exact heq
      have hpt := congrFun heq' 2
      simp [m, Pi.mulSingle_apply, mul_comm] at hpt
      exact hc11 hpt
  have hsk1 : s ^ k = 1 := by
    rw [← hsk, hr0, zpow_zero]
  have hzphi : ((z : Q) : X) = φ (fun _ => x 0) := by
    rw [hzdecomp, hsk1, mul_one, hxconst]
  have hc0mem : φ (fun _ => x 0) ∈ P := hzphi ▸ hzP'
  have hc01 : x 0 ≠ 1 := by
    intro h
    apply hzX1
    rw [hzphi, h, show (fun _ : Fin 3 => (1 : C)) = 1 from rfl, map_one]
  have hc03 : (x 0) ^ 3 = 1 := by
    have hz3 : ((z : Q) : X) ^ 3 = 1 := hPelem.2 ((z : Q) : X) hzP'
    rw [hzphi] at hz3
    have hpow : (fun _ : Fin 3 => x 0) ^ 3 = (fun _ => (x 0) ^ 3) := by
      funext i; simp
    have hthis : φ (fun _ => (x 0) ^ 3) = 1 := by
      rw [← hpow, map_pow]
      exact hz3
    have hphi_eq : φ (fun _ => (x 0) ^ 3) = φ (fun _ => (1 : C)) := by
      rw [hthis, show (fun _ : Fin 3 => (1 : C)) = 1 from rfl, map_one]
    simpa using congrFun (hφ hphi_eq) 0
  exact ⟨x 0, hc01, hc03, hc0mem⟩


private lemma k335crd_coord_test {C : Type} [CommGroup C] {c : C} (hord : orderOf c = 3)
    {w : Fin 3 → C} (f : Fin 3 → ZMod 3) (hwf : ∀ i, w i = c ^ ((f i).val : ℤ))
    {p q : ZMod 3 × ZMod 3 × ZMod 3} (t : Fin 3)
    (h : ((w ^ ((p.1.val : ℕ) : ℤ)) * ((fun i => w (i - 1)) ^ ((p.2.1.val : ℕ) : ℤ)) *
          ((fun i => w (i - 2)) ^ ((p.2.2.val : ℕ) : ℤ))) t =
        ((w ^ ((q.1.val : ℕ) : ℤ)) * ((fun i => w (i - 1)) ^ ((q.2.1.val : ℕ) : ℤ)) *
          ((fun i => w (i - 2)) ^ ((q.2.2.val : ℕ) : ℤ))) t) :
    p.1 * f t + p.2.1 * f (t - 1) + p.2.2 * f (t - 2) =
      q.1 * f t + q.2.1 * f (t - 1) + q.2.2 * f (t - 2) := by
  simp only [Pi.mul_apply, Pi.pow_apply, hwf] at h
  rw [← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul] at h
  rw [← zpow_add, ← zpow_add, ← zpow_add, ← zpow_add] at h
  rw [zpow_eq_zpow_iff_modEq, hord] at h
  rw [← ZMod.intCast_eq_intCast_iff] at h
  push_cast at h
  simpa [mul_comm] using h


private theorem k335crd_circulant_kernel (f : Fin 3 → ZMod 3)
    (hf : f 0 + f 1 + f 2 ≠ 0) :
    ∀ a b c : ZMod 3,
      a * f 0 + b * f 2 + c * f 1 = 0 →
      a * f 1 + b * f 0 + c * f 2 = 0 →
      a * f 2 + b * f 1 + c * f 0 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 := by
  revert f
  decide +kernel

private lemma k335crd_hwf {C : Type} [CommGroup C] {c : C} (hc3 : c ^ 3 = 1)
    (hc1 : c ≠ 1) {u : Fin 3 → C} {e : Fin 3 → ℤ} (he : ∀ i, c ^ e i = u i)
    (w : Fin 3 → C) (hw : ∀ i, w i = u i * c⁻¹) :
    ∀ i, w i = c ^ (((fun i => ((e i - 1 : ℤ) : ZMod 3)) i).val : ℤ) := by
  intro i
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  rw [hw i, ← he i, ← zpow_neg_one, ← zpow_add]
  rw [zpow_eq_zpow_iff_modEq, hord]
  rw [← ZMod.intCast_eq_intCast_iff]
  simp [ZMod.natCast_val]
  ring

attribute [local instance] Fintype.ofFinite in
private theorem k335crd_final {X C : Type} [Group X] [Finite X] [CommGroup C] [Finite C]
    {φ : (Fin 3 → C) →* X} (hφ : Function.Injective φ) {s : X} (_hs3 : s ^ 3 = 1)
    (hs : ∀ x : Fin 3 → C, s * φ x * s⁻¹ = φ (fun i => x (i - 1)))
    {P : Subgroup X} (hPcard : Nat.card P = 9)
    (hPclosed : CFSG.Open.fusionStronglyClosed (P : Set X)
      (φ.range ⊔ Subgroup.zpowers s))
    (hmove : ∀ c : C, c ^ 3 = 1 → c ≠ 1 → ∃ g : X, ∃ u : Fin 3 → C,
      (∀ i, u i ∈ Subgroup.zpowers c) ∧ u 0 * u 1 * u 2 ≠ 1 ∧
        g * φ (fun _ => c) * g⁻¹ = φ u)
    {c : C} (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1)
    (hdiag : φ (fun _ => c) ∈ P) : False := by
  classical
  obtain ⟨g, u, hu_mem, hu_sum, hg⟩ := hmove c hc3 hc1
  have hphiuP : φ u ∈ P := by
    have hmemQ : g * φ (fun _ => c) * g⁻¹ ∈
        (φ.range ⊔ Subgroup.zpowers s : Subgroup X) := by
      rw [hg]
      exact Subgroup.mem_sup_left ⟨u, rfl⟩
    have := hPclosed (φ (fun _ => c)) hdiag (g⁻¹) (by simpa [inv_inv] using hmemQ)
    simpa [inv_inv, hg] using this
  let w : Fin 3 → C := u * (fun _ => c)⁻¹
  have hw_apply : ∀ i, w i = u i * c⁻¹ := by
    intro i; simp [w]
  have hwP : φ w ∈ P := by
    have hphiw : φ w = φ u * (φ (fun _ => c))⁻¹ := by
      simp [w, map_mul, map_inv]
    rw [hphiw]
    exact P.mul_mem hphiuP (P.inv_mem hdiag)
  have hσwP : φ (fun i => w (i - 1)) ∈ P := by
    have hmemQ : (s⁻¹)⁻¹ * φ w * s⁻¹ ∈
        (φ.range ⊔ Subgroup.zpowers s : Subgroup X) := by
      rw [inv_inv, hs w]
      exact Subgroup.mem_sup_left ⟨_, rfl⟩
    have := hPclosed (φ w) hwP (s⁻¹) (by simpa using hmemQ)
    simpa [inv_inv, hs w] using this
  have hσ2wP : φ (fun i => w (i - 2)) ∈ P := by
    have hmemQ : (s⁻¹)⁻¹ * φ (fun i => w (i - 1)) * s⁻¹ ∈
        (φ.range ⊔ Subgroup.zpowers s : Subgroup X) := by
      rw [inv_inv, hs (fun i => w (i - 1))]
      exact Subgroup.mem_sup_left ⟨_, rfl⟩
    have hmem := hPclosed (φ (fun i => w (i - 1))) hσwP (s⁻¹)
      (by simpa using hmemQ)
    have hfun_eq : (fun i => (fun j => w (j - 1)) (i - 1)) = (fun i => w (i - 2)) := by
      funext i
      fin_cases i <;> rfl
    simpa [inv_inv, hs (fun i => w (i - 1)), hfun_eq] using hmem
  choose e he using fun i => Subgroup.mem_zpowers_iff.1 (hu_mem i)
  let f : Fin 3 → ZMod 3 := fun i => ((e i - 1 : ℤ) : ZMod 3)
  have hwf : ∀ i, w i = c ^ ((f i).val : ℤ) :=
    k335crd_hwf hc3 hc1 he w hw_apply
  have hordc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hf : f 0 + f 1 + f 2 ≠ 0 := by
    intro hsum
    apply hu_sum
    have hprod : u 0 * u 1 * u 2 = c ^ (e 0 + e 1 + e 2) := by
      rw [← he 0, ← he 1, ← he 2, ← zpow_add, ← zpow_add]
    rw [hprod, zpow_eq_one_iff_modEq, hordc, Int.modEq_zero_iff_dvd]
    have hsum' : ((e 0 - 1 : ℤ) : ZMod 3) + ((e 1 - 1 : ℤ) : ZMod 3) +
        ((e 2 - 1 : ℤ) : ZMod 3) = 0 := by
      simpa [f] using hsum
    have hsum'' : ((e 0 + e 1 + e 2 : ℤ) : ZMod 3) = 0 := by
      have hdvd1 : (3 : ℤ) ∣ ((e 0 - 1) + (e 1 - 1) + (e 2 - 1)) := by
        have hc : (((e 0 - 1) + (e 1 - 1) + (e 2 - 1) : ℤ) : ZMod 3) = 0 := by
          push_cast
          have h' := hsum'
          push_cast at h'
          exact h'
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hc
      have hdvd : (3 : ℤ) ∣ (e 0 + e 1 + e 2) := by
        have hEq : (e 0 + e 1 + e 2) =
            ((e 0 - 1) + (e 1 - 1) + (e 2 - 1)) + 3 := by ring
        rw [hEq]
        exact dvd_add hdvd1 (dvd_refl 3)
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hdvd
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hsum''
  let F : (ZMod 3 × ZMod 3 × ZMod 3) → P := fun p =>
    ⟨(φ w) ^ ((p.1.val : ℕ) : ℤ) *
        (φ (fun i => w (i - 1))) ^ ((p.2.1.val : ℕ) : ℤ) *
        (φ (fun i => w (i - 2))) ^ ((p.2.2.val : ℕ) : ℤ), by
      refine P.mul_mem (P.mul_mem ?_ ?_) ?_
      · exact P.zpow_mem hwP _
      · exact P.zpow_mem hσwP _
      · exact P.zpow_mem hσ2wP _⟩
  have hcardP : Fintype.card P = 9 := by
    rw [← Nat.card_eq_fintype_card, hPcard]
  have hdom : Fintype.card (ZMod 3 × ZMod 3 × ZMod 3) = 27 := by
    simp [Fintype.card_prod, ZMod.card]
  have hlt : Fintype.card P < Fintype.card (ZMod 3 × ZMod 3 × ZMod 3) := by
    omega
  obtain ⟨p, q, hpq, hFeq⟩ := Fintype.exists_ne_map_eq_of_card_lt F hlt
  have hXeq : (φ w) ^ ((p.1.val : ℕ) : ℤ) *
        (φ (fun i => w (i - 1))) ^ ((p.2.1.val : ℕ) : ℤ) *
        (φ (fun i => w (i - 2))) ^ ((p.2.2.val : ℕ) : ℤ) =
      (φ w) ^ ((q.1.val : ℕ) : ℤ) *
        (φ (fun i => w (i - 1))) ^ ((q.2.1.val : ℕ) : ℤ) *
        (φ (fun i => w (i - 2))) ^ ((q.2.2.val : ℕ) : ℤ) := by
    simpa [F] using congrArg Subtype.val hFeq
  have hfun : (w ^ ((p.1.val : ℕ) : ℤ)) *
        ((fun i => w (i - 1)) ^ ((p.2.1.val : ℕ) : ℤ)) *
        ((fun i => w (i - 2)) ^ ((p.2.2.val : ℕ) : ℤ)) =
      (w ^ ((q.1.val : ℕ) : ℤ)) *
        ((fun i => w (i - 1)) ^ ((q.2.1.val : ℕ) : ℤ)) *
        ((fun i => w (i - 2)) ^ ((q.2.2.val : ℕ) : ℤ)) := by
    apply hφ
    simpa [map_mul, map_zpow] using hXeq
  have hcoord : ∀ t : Fin 3,
      p.1 * f t + p.2.1 * f (t - 1) + p.2.2 * f (t - 2) =
        q.1 * f t + q.2.1 * f (t - 1) + q.2.2 * f (t - 2) :=
    fun t => k335crd_coord_test hordc f hwf t (congrFun hfun t)
  have h01 : (0 : Fin 3) - 1 = 2 := by decide
  have h02 : (0 : Fin 3) - 2 = 1 := by decide
  have h11 : (1 : Fin 3) - 1 = 0 := by decide
  have h12 : (1 : Fin 3) - 2 = 2 := by decide
  have h21 : (2 : Fin 3) - 1 = 1 := by decide
  have h22 : (2 : Fin 3) - 2 = 0 := by decide
  have h0 : p.1 * f 0 + p.2.1 * f 2 + p.2.2 * f 1 =
      q.1 * f 0 + q.2.1 * f 2 + q.2.2 * f 1 := by
    have := hcoord 0
    rw [h01, h02] at this
    simpa using this
  have h1 : p.1 * f 1 + p.2.1 * f 0 + p.2.2 * f 2 =
      q.1 * f 1 + q.2.1 * f 0 + q.2.2 * f 2 := by
    have := hcoord 1
    rw [h11, h12] at this
    simpa using this
  have h2 : p.1 * f 2 + p.2.1 * f 1 + p.2.2 * f 0 =
      q.1 * f 2 + q.2.1 * f 1 + q.2.2 * f 0 := by
    have := hcoord 2
    rw [h21, h22] at this
    simpa using this
  have e0 : (p.1 - q.1) * f 0 + (p.2.1 - q.2.1) * f 2 +
      (p.2.2 - q.2.2) * f 1 = 0 := by
    linear_combination h0
  have e1 : (p.1 - q.1) * f 1 + (p.2.1 - q.2.1) * f 0 +
      (p.2.2 - q.2.2) * f 2 = 0 := by
    linear_combination h1
  have e2 : (p.1 - q.1) * f 2 + (p.2.1 - q.2.1) * f 1 +
      (p.2.2 - q.2.2) * f 0 = 0 := by
    linear_combination h2
  obtain ⟨ha, hb, hcc⟩ :=
    k335crd_circulant_kernel f hf (p.1 - q.1) (p.2.1 - q.2.1) (p.2.2 - q.2.2) e0 e1 e2
  have hp1 : p.1 = q.1 := sub_eq_zero.mp ha
  have hp2 : p.2.1 = q.2.1 := sub_eq_zero.mp hb
  have hp3 : p.2.2 = q.2.2 := sub_eq_zero.mp hcc
  exact hpq (Prod.ext hp1 (Prod.ext hp2 hp3))

theorem k335_noStrong_of_coord {X C : Type} [Group X] [Finite X] [CommGroup C] [Finite C]
    {a : ℕ} (ha : 1 ≤ a) (hC : Nat.card C = 3 ^ a) {φ : (Fin 3 → C) →* X}
    (hφ : Function.Injective φ) {s : X} (hs3 : s ^ 3 = 1)
    (hs : ∀ x : Fin 3 → C, s * φ x * s⁻¹ = φ (fun i => x (i - 1)))
    (hX : ¬ 3 ^ (3 * a + 2) ∣ Nat.card X)
    (hmove : ∀ c : C, c ^ 3 = 1 → c ≠ 1 → ∃ g : X, ∃ u : Fin 3 → C,
      (∀ i, u i ∈ Subgroup.zpowers c) ∧ u 0 * u 1 * u 2 ≠ 1 ∧ g * φ (fun _ => c) * g⁻¹ = φ u) :
    K335NoStrongE9 X := by
  intro P S hS
  obtain ⟨hPleS, hSsyl, hPelem, hPcard, hPclosedS⟩ := hS
  let Q : Subgroup X := φ.range ⊔ Subgroup.zpowers s
  have hQcard : Nat.card Q = 3 ^ (3 * a + 1) := by
    rw [show Q = φ.range ⊔ Subgroup.zpowers s from rfl]
    exact k335crd_card_Q ha hC hφ hs3 hs
  have hfac : (Nat.card X).factorization 3 = 3 * a + 1 := by
    apply Nat.le_antisymm
    · by_contra hle
      push Not at hle
      have hle' : 3 * a + 2 ≤ (Nat.card X).factorization 3 := by omega
      exact hX ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
        (Nat.card_pos (α := X)).ne').mpr hle')
    · have hdvd : 3 ^ (3 * a + 1) ∣ Nat.card X := by
        rw [← hQcard]
        exact ⟨Q.index, (Subgroup.card_mul_index Q).symm⟩
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
        (Nat.card_pos (α := X)).ne').mp hdvd
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q ⊤ := by
    apply CFSG.ABGLocalTools.isSylowOf_of_card le_top
    rw [hQcard, Subgroup.card_top, hfac]
  have hQp : IsPGroup 3 Q := hQsyl.isPGroup
  have hQidx : ¬ 3 ∣ Q.index := by
    simpa [Subgroup.relIndex_top_right] using (CFSG.ABGLocalTools.isSylowOf_iff.1 hQsyl).2.2
  have hSp : IsPGroup 3 S := hSsyl.isPGroup
  have hSidx : ¬ 3 ∣ S.index := by
    simpa [Subgroup.relIndex_top_right] using (CFSG.ABGLocalTools.isSylowOf_iff.1 hSsyl).2.2
  let Qs : Sylow 3 X := hQp.toSylow hQidx
  let Ss : Sylow 3 X := hSp.toSylow hSidx
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq X Qs Ss
  have hcoe : (MulAut.conj y) • (Q : Set X) = (S : Set X) := by
    have h1 := congrArg (fun T : Sylow 3 X => (T : Set X)) hy
    rw [Sylow.coe_smul] at h1
    change MulAut.conj y • (Q : Set X) = (S : Set X) at h1
    exact h1
  let e : X ≃* X := MulAut.conj y
  have hmap : Q.map e.toMonoidHom = S := by
    change Q.map (MulAut.conj y).toMonoidHom = S
    ext z
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hmem : (MulAut.conj y) q ∈ (MulAut.conj y) • (Q : Set X) := by
        rw [Set.mem_smul_set]
        exact ⟨q, hq, rfl⟩
      rwa [hcoe] at hmem
    · intro hz
      have hmem : z ∈ (MulAut.conj y) • (Q : Set X) := by rwa [hcoe]
      rw [Set.mem_smul_set] at hmem
      obtain ⟨q, hq, hqeq⟩ := hmem
      exact ⟨q, hq, by simpa [e] using hqeq⟩
  let φ' : (Fin 3 → C) →* X := e.toMonoidHom.comp φ
  let s' : X := e s
  have hφ' : Function.Injective φ' := e.injective.comp hφ
  have hs3' : s' ^ 3 = 1 := by
    rw [show s' = e s from rfl, ← map_pow, hs3, map_one]
  have hs' : ∀ x : Fin 3 → C, s' * φ' x * s'⁻¹ = φ' (fun i => x (i - 1)) := by
    intro x
    simpa [φ', s', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul, map_inv]
      using congrArg e (hs x)
  have hmove' : ∀ c : C, c ^ 3 = 1 → c ≠ 1 → ∃ g : X, ∃ u : Fin 3 → C,
      (∀ i, u i ∈ Subgroup.zpowers c) ∧ u 0 * u 1 * u 2 ≠ 1 ∧
        g * φ' (fun _ => c) * g⁻¹ = φ' u := by
    intro c hc3 hc1
    obtain ⟨g, u, hu, hu1, hg⟩ := hmove c hc3 hc1
    refine ⟨e g, u, hu, hu1, ?_⟩
    simp only [φ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_inv, ← map_mul, ← map_mul, hg]
  have hQ' : φ'.range ⊔ Subgroup.zpowers s' = S := by
    have hr : φ'.range = φ.range.map e.toMonoidHom := by
      rw [show φ' = e.toMonoidHom.comp φ from rfl, MonoidHom.range_comp]
    have hzp : Subgroup.zpowers s' = (Subgroup.zpowers s).map e.toMonoidHom :=
      (MonoidHom.map_zpowers e.toMonoidHom s).symm
    rw [hr, hzp, ← Subgroup.map_sup, hmap]
  have hPle' : P ≤ φ'.range ⊔ Subgroup.zpowers s' := by rw [hQ']; exact hPleS
  have hPclosed' : CFSG.Open.fusionStronglyClosed (P : Set X)
      (φ'.range ⊔ Subgroup.zpowers s') := by rw [hQ']; exact hPclosedS
  obtain ⟨c0, hc01, hc03, hdiag⟩ :=
    k335crd_center_element ha hC hφ' hs3' hs' hPle' hPcard hPelem hPclosed'
  exact k335crd_final hφ' hs3' hs' hPcard hPclosed' hmove' hc01 hc03 hdiag

theorem k335_noStrong_of_coordData {X : Type} [Group X] [Finite X] {a : ℕ} (ha : 1 ≤ a)
    (hc : K335Coord X a) (hX : ¬ 3 ^ (3 * a + 2) ∣ Nat.card X) : K335NoStrongE9 X := by
  obtain ⟨C, _, _, hC, φ, hφ, s, hs3, hs, hmove⟩ := hc
  exact k335_noStrong_of_coord ha hC hφ hs3 hs hX hmove

theorem k335_two_mul_card_alt {X : Type} [Group X] {n : ℕ}
    (h : Nonempty (X ≃* alternatingGroup (Fin n))) (hn : 2 ≤ n) :
    2 * Nat.card X = n.factorial := by
  obtain ⟨e⟩ := h
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, two_mul_card_alternatingGroup,
    Fintype.card_perm, Fintype.card_fin]

private abbrev k335alt_C := Multiplicative (ZMod 3)

private def k335alt_cyc (x y z : Fin 9) : Equiv.Perm (Fin 9) :=
  Equiv.swap x y * Equiv.swap y z

private def k335alt_a : alternatingGroup (Fin 9) :=
  ⟨k335alt_cyc 0 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; simp [k335alt_cyc]⟩

private def k335alt_b : alternatingGroup (Fin 9) :=
  ⟨k335alt_cyc 3 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; simp [k335alt_cyc]⟩

private def k335alt_c : alternatingGroup (Fin 9) :=
  ⟨k335alt_cyc 6 7 8, by rw [Equiv.Perm.mem_alternatingGroup]; simp [k335alt_cyc]⟩

private def k335alt_s : alternatingGroup (Fin 9) :=
  ⟨k335alt_cyc 0 3 6 * k335alt_cyc 1 4 7 * k335alt_cyc 2 5 8, by
    rw [Equiv.Perm.mem_alternatingGroup]; simp [k335alt_cyc]⟩

private def k335alt_g : alternatingGroup (Fin 9) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 3 4, by
    rw [Equiv.Perm.mem_alternatingGroup]; simp⟩

private def k335alt_phiFun (x : Fin 3 → k335alt_C) : alternatingGroup (Fin 9) :=
  ⟨(k335alt_a : Equiv.Perm (Fin 9)) ^ (x 0).toAdd.val *
   (k335alt_b : Equiv.Perm (Fin 9)) ^ (x 1).toAdd.val *
   (k335alt_c : Equiv.Perm (Fin 9)) ^ (x 2).toAdd.val, by
    rw [Equiv.Perm.mem_alternatingGroup]
    simp [k335alt_a, k335alt_b, k335alt_c, k335alt_cyc]⟩

private lemma k335alt_phi_mul : ∀ x y : Fin 3 → k335alt_C,
    k335alt_phiFun (x * y) = k335alt_phiFun x * k335alt_phiFun y := by
  decide +kernel

private def k335alt_phi : (Fin 3 → k335alt_C) →* alternatingGroup (Fin 9) :=
  MonoidHom.mk' k335alt_phiFun k335alt_phi_mul

private lemma k335alt_phi_inj : Function.Injective k335alt_phi := by
  rw [injective_iff_map_eq_one]
  decide +kernel

private lemma k335alt_s3 : k335alt_s ^ 3 = 1 := by
  apply Subtype.ext
  ext i
  fin_cases i <;> decide

private lemma k335alt_shift : ∀ x : Fin 3 → k335alt_C,
    k335alt_s * k335alt_phi x * k335alt_s⁻¹ = k335alt_phi (fun i => x (i - 1)) := by
  decide +kernel

private def k335alt_u (c : k335alt_C) : Fin 3 → k335alt_C :=
  fun i => if i = 2 then c else c ^ 2

private lemma k335alt_move_eq : ∀ c : k335alt_C, c ^ 3 = 1 → c ≠ 1 →
    k335alt_g * k335alt_phi (fun _ => c) * k335alt_g⁻¹ = k335alt_phi (k335alt_u c) := by
  decide +kernel

private lemma k335alt_u_mem (c : k335alt_C) (i : Fin 3) :
    k335alt_u c i ∈ Subgroup.zpowers c := by
  fin_cases i <;> simp [k335alt_u]

private lemma k335alt_u_prod (c : k335alt_C) (hc3 : c ^ 3 = 1) :
    k335alt_u c 0 * k335alt_u c 1 * k335alt_u c 2 = c ^ 2 := by
  simp [k335alt_u]
  rw [show c ^ 2 * c ^ 2 * c = c ^ 5 by group]
  rw [show (5 : ℕ) = 3 + 2 from rfl, pow_add, hc3, one_mul]

private lemma k335alt_c_sq_ne_one (c : k335alt_C) (hc : c ≠ 1) : c ^ 2 ≠ 1 := by
  intro h
  have h2 : orderOf c ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
  have h3 : orderOf c ∣ 3 := by
    simpa [k335alt_C] using orderOf_dvd_natCard c
  have h1 : orderOf c ∣ 1 := by
    simpa using Nat.dvd_gcd h2 h3
  exact hc (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1))

private lemma k335alt_card_C : Nat.card k335alt_C = 3 ^ 1 := by simp [k335alt_C]

private theorem k335alt_coord_A9 : K335Coord (alternatingGroup (Fin 9)) 1 := by
  refine ⟨k335alt_C, inferInstance, inferInstance, k335alt_card_C, k335alt_phi,
    k335alt_phi_inj, k335alt_s, k335alt_s3, k335alt_shift, ?_⟩
  intro c hc3 hc1
  exact ⟨k335alt_g, k335alt_u c, fun i => k335alt_u_mem c i,
    by
      intro h
      exact k335alt_c_sq_ne_one c hc1 (by rw [← k335alt_u_prod c hc3]; exact h),
    k335alt_move_eq c hc3 hc1⟩

private theorem k335alt_coord_An {n : ℕ} (hn : 9 ≤ n) :
    K335Coord (alternatingGroup (Fin n)) 1 := by
  let f : Fin 9 ≃ Subtype (fun x : Fin n => x ∈ Set.range (Fin.castLEEmb hn)) :=
    (Fin.castLEEmb hn).toEquivRange
  let ψP : alternatingGroup (Fin 9) →* Equiv.Perm (Fin n) :=
    (Equiv.Perm.extendDomainHom f).comp (alternatingGroup (Fin 9)).subtype
  let ψ : alternatingGroup (Fin 9) →* alternatingGroup (Fin n) :=
    ψP.codRestrict _ (fun x => by
      rw [Equiv.Perm.mem_alternatingGroup]
      change Equiv.Perm.sign ((Equiv.Perm.extendDomainHom f) x.1) = 1
      rw [show (Equiv.Perm.extendDomainHom f) x.1 = x.1.extendDomain f from rfl]
      rw [Equiv.Perm.sign_extendDomain]
      exact Equiv.Perm.mem_alternatingGroup.mp x.2)
  have hψ : Function.Injective ψ := by
    rw [MonoidHom.injective_codRestrict]
    exact (Equiv.Perm.extendDomainHom_injective f).comp Subtype.coe_injective
  have hker : Nat.card ψ.ker = 1 := by
    rw [(MonoidHom.ker_eq_bot_iff ψ).mpr hψ, Subgroup.card_bot]
  refine K335Coord.map ψ ?_ k335alt_coord_A9
  rw [hker]
  norm_num

theorem k335_coord_alt {X : Type} [Group X] {n : ℕ}
    (h : Nonempty (X ≃* alternatingGroup (Fin n))) (hn : 9 ≤ n) : K335Coord X 1 := by
  obtain ⟨e⟩ := h
  exact K335Coord.of_mulEquiv e.symm (k335alt_coord_An hn)

theorem k335_noStrong_alt {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : Nonempty (X ≃* alternatingGroup (Fin n))) (hn : 9 ≤ n) (hn' : n ≤ 11) :
    K335NoStrongE9 X := by
  refine k335_noStrong_of_coordData le_rfl (k335_coord_alt h hn) ?_
  have h2 := k335_two_mul_card_alt h (by omega)
  interval_cases n <;> norm_num [Nat.factorial] at h2 ⊢ <;> omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
