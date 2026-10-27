module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Frame
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.EmptyFaithful.S153DGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s16h_e3_fp_finite_mulAut (W : Type) [Group W] [Finite W] : Finite (MulAut W) :=
  Finite.of_injective (fun f : MulAut W => (f : W → W))
    (fun f g h => MulEquiv.ext (congrFun h))

private theorem s16h_e3_fp_centralizer_sup {W : Type} [CommGroup W]
    (L L' : Subgroup (MulAut W)) :
    Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W)) =
      Subgroup.centralizer (L : Set (MulAut W)) ⊓
        Subgroup.centralizer (L' : Set (MulAut W)) := by
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Subgroup.mem_sup_left ha),
      fun b hb => h b (Subgroup.mem_sup_right hb)⟩
  · rintro ⟨h1, h2⟩
    have hL1 : L ≤ Subgroup.centralizer ({x} : Set (MulAut W)) :=
      fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (h1 a ha)
    have hL2 : L' ≤ Subgroup.centralizer ({x} : Set (MulAut W)) :=
      fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (h2 a ha)
    have hsup : L ⊔ L' ≤ Subgroup.centralizer ({x} : Set (MulAut W)) := sup_le hL1 hL2
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hsup hy)

private theorem s16h_e3_fp_mem_normalizer {W : Type} [CommGroup W]
    {L L' : Subgroup (MulAut W)} {e : MulAut W} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : e ^ p = 1)
    (hperm : (L.map (MulAut.conj e).toMonoidHom = L ∧
        L'.map (MulAut.conj e).toMonoidHom = L') ∨
      (L.map (MulAut.conj e).toMonoidHom = L' ∧
        L'.map (MulAut.conj e).toMonoidHom = L)) :
    e ∈ normalizer (L : Set (MulAut W)) ∧ e ∈ normalizer (L' : Set (MulAut W)) := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hcomp : (MulAut.conj e).toMonoidHom.comp (MulAut.conj e).toMonoidHom =
      (MulAut.conj (e ^ 2)).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    show MulAut.conj e (MulAut.conj e x) = MulAut.conj (e ^ 2) x
    rw [← MulAut.mul_apply, ← map_mul (MulAut.conj) e e, pow_two]
  have key : ∀ A B : Subgroup (MulAut W),
      A.map (MulAut.conj e).toMonoidHom = B → B.map (MulAut.conj e).toMonoidHom = A →
      e ∈ normalizer (A : Set (MulAut W)) := by
    intro A B hAB hBA
    refine S153D.mem_normalizer_of_sq_mem
      (hodd.of_dvd_nat (orderOf_dvd_iff_pow_eq_one.mpr he)) ?_
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : (A.map (MulAut.conj e).toMonoidHom).map (MulAut.conj e).toMonoidHom = A := by
      rw [hAB, hBA]
    rwa [Subgroup.map_map, hcomp] at h1
  rcases hperm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨key L L h1 h1, key L' L' h2 h2⟩
  · exact ⟨key L L' h1 h2, key L' L h2 h1⟩

private theorem s16h_e3_fp_center_eq_bot_of_centerless {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)}
    (hcen : ∀ a ∈ L, (∀ b ∈ L, a * b = b * a) → a = 1) :
    Subgroup.center ↥L = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  exact hcen (x : MulAut W) x.2 (fun b hb => by
    have h := Subgroup.mem_center_iff.mp hx (⟨b, hb⟩ : ↥L)
    exact (congrArg Subtype.val h).symm)

private theorem s16h_e3_fp_centerless_of_iso {W : Type} [CommGroup W]
    {L L' : Subgroup (MulAut W)} (e : ↥L ≃* ↥L')
    (hcen : ∀ a ∈ L, (∀ b ∈ L, a * b = b * a) → a = 1) :
    ∀ a ∈ L', (∀ b ∈ L', a * b = b * a) → a = 1 := by
  have hcenterL : Subgroup.center ↥L = ⊥ := s16h_e3_fp_center_eq_bot_of_centerless hcen
  have hcenterL' : Subgroup.center ↥L' = ⊥ := by
    rw [← Subgroup.map_center_eq e, hcenterL]
    exact Subgroup.map_bot e.toMonoidHom
  intro a ha hcomm
  have hmem : (⟨a, ha⟩ : ↥L') ∈ Subgroup.center ↥L' := by
    rw [Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    exact (hcomm (b : MulAut W) b.2).symm
  rw [hcenterL'] at hmem
  have h1 : (⟨a, ha⟩ : ↥L') = 1 := by simpa using hmem
  exact Subtype.ext_iff.mp h1

private theorem s16h_e3_fp_ker_card {W : Type} [CommGroup W] [Finite W]
    {A : Subgroup (MulAut W)} {E : Subgroup (MulAut W)} {p : ℕ} (hp : p.Prime)
    (hEN : E ≤ normalizer (A : Set (MulAut W))) (hcardE : Nat.card ↥E = p ^ 3)
    (hAut : ¬ p ^ 2 ∣ Nat.card (MulAut ↥A)) :
    p ^ 2 ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (A : Set (MulAut W))) := by
  classical
  haveI : Finite (MulAut W) := s16h_e3_fp_finite_mulAut W
  let φ : E →* MulAut ↥A := (Subgroup.normalizerMonoidHom A).comp (Subgroup.inclusion hEN)
  have hker : φ.ker = (E ⊓ Subgroup.centralizer (A : Set (MulAut W))).subgroupOf E := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : (⟨(x : MulAut W), hEN x.2⟩ : normalizer (A : Set (MulAut W))) ∈
          (Subgroup.normalizerMonoidHom A).ker := hx
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hx'
      exact ⟨x.2, hx'⟩
    · rintro ⟨-, hxcent⟩
      show (Subgroup.normalizerMonoidHom A) (Subgroup.inclusion hEN x) = 1
      have hmem : (⟨(x : MulAut W), hEN x.2⟩ : normalizer (A : Set (MulAut W))) ∈
          (Subgroup.normalizerMonoidHom A).ker := by
        rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
        exact hxcent
      exact hmem
  have hdvd : Nat.card φ.range ∣ p ^ 3 := by
    have h := card_ker_mul_card_range φ
    rw [hcardE] at h
    exact ⟨Nat.card φ.ker, by rw [mul_comm]; exact h.symm⟩
  have hdvdAut : Nat.card φ.range ∣ Nat.card (MulAut ↥A) :=
    Subgroup.card_subgroup_dvd_card φ.range
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hkAut : p ^ k ∣ Nat.card (MulAut ↥A) := by rw [← hk]; exact hdvdAut
  have hk2 : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := by omega
    exact hAut ((pow_dvd_pow p h2).trans hkAut)
  have hrange : Nat.card φ.range ≤ p := by
    rw [hk]
    calc p ^ k ≤ p ^ 1 := pow_le_pow_right₀ (le_of_lt hp.one_lt) hk2
      _ = p := pow_one p
  have h := card_ker_mul_card_range φ
  rw [hker, hcardE] at h
  have hcardker : Nat.card ↥((E ⊓ Subgroup.centralizer (A : Set (MulAut W))).subgroupOf E) =
      Nat.card ↥(E ⊓ Subgroup.centralizer (A : Set (MulAut W))) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hcardker] at h
  have hle : p ^ 2 * p ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (A : Set (MulAut W))) * p := by
    have h2 : p ^ 2 * p = p ^ 3 := by ring
    rw [h2, ← h]
    exact Nat.mul_le_mul_left _ hrange
  exact Nat.le_of_mul_le_mul_right hle hp.pos

private theorem s16h_e3_fp_three_le_card_inf {W : Type} [CommGroup W] [Finite W]
    {E A B : Subgroup (MulAut W)} {p : ℕ} (hp : p.Prime) (hA : A ≤ E) (hB : B ≤ E)
    (hcardE : Nat.card ↥E = p ^ 3) (hA2 : p ^ 2 ≤ Nat.card ↥A)
    (hB2 : p ^ 2 ≤ Nat.card ↥B) :
    p ≤ Nat.card ↥(A ⊓ B) := by
  have hArel : A.relIndex E ≤ p := by
    have h := Subgroup.relIndex_mul_card A E
    have hEA : A ⊓ E = A := inf_eq_left.mpr hA
    rw [hEA, hcardE] at h
    have hle : A.relIndex E * p ^ 2 ≤ p * p ^ 2 := by
      calc A.relIndex E * p ^ 2 ≤ A.relIndex E * Nat.card ↥A := Nat.mul_le_mul_left _ hA2
        _ = p ^ 3 := h
        _ = p * p ^ 2 := by ring
    exact Nat.le_of_mul_le_mul_right hle (pow_pos hp.pos 2)
  have hBrel : B.relIndex E ≤ p := by
    have h := Subgroup.relIndex_mul_card B E
    have hEB : B ⊓ E = B := inf_eq_left.mpr hB
    rw [hEB, hcardE] at h
    have hle : B.relIndex E * p ^ 2 ≤ p * p ^ 2 := by
      calc B.relIndex E * p ^ 2 ≤ B.relIndex E * Nat.card ↥B := Nat.mul_le_mul_left _ hB2
        _ = p ^ 3 := h
        _ = p * p ^ 2 := by ring
    exact Nat.le_of_mul_le_mul_right hle (pow_pos hp.pos 2)
  have hABrel : (A ⊓ B).relIndex E ≤ p ^ 2 := by
    calc (A ⊓ B).relIndex E ≤ A.relIndex E * B.relIndex E :=
          Subgroup.relIndex_inf_le (H := A) (K := B) (L := E)
      _ ≤ p * p := Nat.mul_le_mul hArel hBrel
      _ = p ^ 2 := by ring
  have h := Subgroup.relIndex_mul_card (A ⊓ B) E
  have hinf : (A ⊓ B) ⊓ E = A ⊓ B := inf_eq_left.mpr (inf_le_left.trans hA)
  rw [hinf, hcardE] at h
  have hle : p * p ^ 2 ≤ Nat.card ↥(A ⊓ B) * p ^ 2 := by
    calc p * p ^ 2 = p ^ 3 := by ring
      _ = (A ⊓ B).relIndex E * Nat.card ↥(A ⊓ B) := h.symm
      _ ≤ p ^ 2 * Nat.card ↥(A ⊓ B) := Nat.mul_le_mul_right _ hABrel
      _ = Nat.card ↥(A ⊓ B) * p ^ 2 := by ring
  exact Nat.le_of_mul_le_mul_right hle (pow_pos hp.pos 2)

theorem s16h_e3_frame_p {W : Type} [CommGroup W] [Finite W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W} (F : s16h_E3Frame X L L' T U U')
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : ∀ a ∈ L, (∀ b ∈ L, a * b = b * a) → a = 1)
    (hpL : p ∣ Nat.card ↥L) (hAut : ¬ p ^ 2 ∣ Nat.card (MulAut ↥L))
    (hrk : ∃ E : Subgroup (MulAut W), E ≤ X ∧ IsElemAbelian p E ∧ Nat.card ↥E = p ^ 3)
    {w : W} (hwU : w ∈ U)
    (hbad : ∀ E : Subgroup (MulAut W), E ≤ X → IsElemAbelian p E → (∀ e ∈ E, e w = w) →
      Nat.card ↥E ≤ p) :
    (∃ d ∈ X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W)),
        orderOf d = p) ∧
      ∀ x ∈ X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W)),
        x ^ p = 1 → x ≠ 1 → (∃ u ∈ U, x u ≠ u) ∧ ∃ u ∈ U', x u ≠ u := by
  classical
  haveI : Finite (MulAut W) := s16h_e3_fp_finite_mulAut W
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEX, hEab, hEcard⟩ := hrk
  obtain ⟨t, htT, hLt, hUt⟩ := F.swap
  have htX : t ∈ X := F.t_le htT
  have hiso : ↥L ≃* ↥L' :=
    (L.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).trans
      (MulEquiv.subgroupCongr hLt)
  have hcardL' : Nat.card ↥L' = Nat.card ↥L := (Nat.card_congr hiso.toEquiv).symm
  have hcardAut' : Nat.card (MulAut ↥L') = Nat.card (MulAut ↥L) :=
    (Nat.card_congr (MulAut.congr hiso).toEquiv).symm
  have hpL' : p ∣ Nat.card ↥L' := by rw [hcardL']; exact hpL
  have hAut' : ¬ p ^ 2 ∣ Nat.card (MulAut ↥L') := by rw [hcardAut']; exact hAut
  have hcen' : ∀ a ∈ L', (∀ b ∈ L', a * b = b * a) → a = 1 :=
    s16h_e3_fp_centerless_of_iso hiso hcen
  have hEN : E ≤ normalizer (L : Set (MulAut W)) := by
    intro e he
    exact (s16h_e3_fp_mem_normalizer hp hp2 (hEab.2 e he) (by
      rcases F.perm e (hEX he) with h | h
      · exact Or.inl ⟨h.1, h.2.1⟩
      · exact Or.inr ⟨h.1, h.2.1⟩)).1
  have hEN' : E ≤ normalizer (L' : Set (MulAut W)) := by
    intro e he
    exact (s16h_e3_fp_mem_normalizer hp hp2 (hEab.2 e he) (by
      rcases F.perm e (hEX he) with h | h
      · exact Or.inl ⟨h.1, h.2.1⟩
      · exact Or.inr ⟨h.1, h.2.1⟩)).2
  have hcent_split := s16h_e3_fp_centralizer_sup (W := W) L L'
  let K : Subgroup (MulAut W) :=
    X ⊓ Subgroup.centralizer (((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W)))
  have hcardA : p ^ 2 ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set (MulAut W))) :=
    s16h_e3_fp_ker_card hp hEN hEcard hAut
  have hcardB : p ^ 2 ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (L' : Set (MulAut W))) :=
    s16h_e3_fp_ker_card hp hEN' hEcard hAut'
  have hEKL : E ⊓ K = (E ⊓ Subgroup.centralizer (L : Set (MulAut W))) ⊓
      (E ⊓ Subgroup.centralizer (L' : Set (MulAut W))) := by
    dsimp only [K]
    rw [hcent_split]
    ext x
    constructor
    · rintro ⟨hxE, -, hxL, hxL'⟩
      exact ⟨⟨hxE, hxL⟩, hxE, hxL'⟩
    · rintro ⟨⟨hxE, hxL⟩, -, hxL'⟩
      exact ⟨hxE, hEX hxE, hxL, hxL'⟩
  have hEKp : p ≤ Nat.card ↥(E ⊓ K) := by
    rw [hEKL]
    exact s16h_e3_fp_three_le_card_inf hp inf_le_left inf_le_left hEcard hcardA hcardB
  have hEKne : E ⊓ K ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(E ⊓ K) = 1 := by rw [hbot]; exact Subgroup.card_bot
    have hp2le : 2 ≤ p := hp.two_le
    omega
  obtain ⟨d, hdEK, hd1⟩ : ∃ d ∈ E ⊓ K, d ≠ (1 : MulAut W) :=
    (Subgroup.bot_or_exists_ne_one (E ⊓ K)).resolve_left hEKne
  rw [Subgroup.mem_inf] at hdEK
  obtain ⟨hdE, hdK⟩ := hdEK
  have hdp : d ^ p = 1 := hEab.2 d hdE
  have hdord : orderOf d = p := by
    have hdvd : orderOf d ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hdp
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hd1
    · exact h
  have hbadw' : ∀ E' : Subgroup (MulAut W), E' ≤ X → IsElemAbelian p E' →
      (∀ e ∈ E', e (t w) = t w) → Nat.card ↥E' ≤ p := by
    intro E' hE'X hE'ab hfix
    have htinv : t⁻¹ ∈ X := X.inv_mem htX
    let E'' : Subgroup (MulAut W) := E'.map (MulAut.conj t⁻¹).toMonoidHom
    have hE''X : E'' ≤ X := by
      intro e he
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp he
      change (MulAut.conj t⁻¹) a ∈ X
      rw [MulAut.conj_apply, inv_inv]
      exact X.mul_mem (X.mul_mem htinv (hE'X ha)) htX
    have hE''ab : IsElemAbelian p E'' := hE'ab.map (MulAut.conj t⁻¹).toMonoidHom
    have hE''fix : ∀ e ∈ E'', e w = w := by
      intro e he
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp he
      change (MulAut.conj t⁻¹) a w = w
      rw [MulAut.conj_apply, inv_inv, MulAut.mul_apply, MulAut.mul_apply, hfix a ha]
      simp
    have hcard := hbad E'' hE''X hE''ab hE''fix
    have hcard' : Nat.card ↥E'' = Nat.card ↥E' :=
      Subgroup.card_map_of_injective (K := E') (MulAut.conj t⁻¹).injective
    rwa [hcard'] at hcard
  have hw'U' : t w ∈ U' := by
    have h : t w ∈ U.map t.toMonoidHom := Subgroup.mem_map_of_mem t.toMonoidHom hwU
    rwa [hUt] at h
  refine ⟨⟨d, ?_, hdord⟩, ?_⟩
  · dsimp only [K] at hdK
    exact hdK
  · intro x hxK hxp hx1
    rw [Subgroup.mem_inf] at hxK
    obtain ⟨hxX, hxcent⟩ := hxK
    have hxcomm : ∀ a ∈ L ⊔ L', x * a = a * x := fun a ha =>
      (Subgroup.mem_centralizer_iff.mp hxcent a ha).symm
    constructor
    · by_contra hxU
      have hxcU : x ∈ centSub U := by
        rw [mem_centSub]
        intro u hu
        by_contra hne
        exact hxU ⟨u, hu, hne⟩
      obtain ⟨y', hy'ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥L') p hpL'
      have hy'p : (y' : MulAut W) ^ p = 1 := by
        have h := pow_orderOf_eq_one y'
        rw [hy'ord] at h
        simpa using congrArg Subtype.val h
      have hy'cent : Commute x (y' : MulAut W) :=
        hxcomm (y' : MulAut W) (Subgroup.mem_sup_right y'.2)
      have hE9ab : IsElemAbelian p
          (Subgroup.zpowers x ⊔ Subgroup.zpowers (y' : MulAut W)) := by
        apply IsElemAbelian.sup_of_commute
        · exact isElemAbelian_zpowers hxp
        · exact isElemAbelian_zpowers hy'p
        · intro a ha b hb
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
          exact (hy'cent.zpow_zpow i j).eq
      have hE9X : Subgroup.zpowers x ⊔ Subgroup.zpowers (y' : MulAut W) ≤ X :=
        sup_le (Subgroup.zpowers_le.mpr hxX) (Subgroup.zpowers_le.mpr (F.le_x' y'.2))
      have hE9fix : ∀ e ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers (y' : MulAut W),
          e w = w := by
        intro e he
        have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers (y' : MulAut W) ≤
            MulAction.stabilizer (MulAut W) w := by
          apply sup_le
          · rw [Subgroup.zpowers_le]
            exact MulAction.mem_stabilizer_iff.mpr
              (by simpa using mem_centSub.mp hxcU w hwU)
          · rw [Subgroup.zpowers_le]
            exact MulAction.mem_stabilizer_iff.mpr
              (by simpa using F.fix_u (y' : MulAut W) y'.2 w hwU)
        exact MulAction.mem_stabilizer_iff.mp (hle he)
      have hbadE9 := hbad _ hE9X hE9ab hE9fix
      have hxnot : x ∉ Subgroup.zpowers (y' : MulAut W) := by
        intro hxmem
        have hxL' : x ∈ L' := (Subgroup.zpowers_le.mpr y'.2) hxmem
        exact hx1 (hcen' x hxL' (fun b hb => hxcomm b (Subgroup.mem_sup_right hb)))
      have hlt : Subgroup.zpowers (y' : MulAut W) <
          Subgroup.zpowers x ⊔ Subgroup.zpowers (y' : MulAut W) := by
        refine lt_of_le_of_ne le_sup_right ?_
        intro heq
        exact hxnot (heq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩))
      have hcardFy : Nat.card ↥(Subgroup.zpowers (y' : MulAut W)) = p := by
        rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy'ord]
      have hplt : p < Nat.card ↥
          (Subgroup.zpowers x ⊔ Subgroup.zpowers (y' : MulAut W)) := by
        rw [← hcardFy]
        exact Subgroup.card_lt_of_lt hlt
      omega
    · by_contra hxU'
      have hxcU' : x ∈ centSub U' := by
        rw [mem_centSub]
        intro u hu
        by_contra hne
        exact hxU' ⟨u, hu, hne⟩
      obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) p hpL
      have hyp : (y : MulAut W) ^ p = 1 := by
        have h := pow_orderOf_eq_one y
        rw [hyord] at h
        simpa using congrArg Subtype.val h
      have hycent : Commute x (y : MulAut W) :=
        hxcomm (y : MulAut W) (Subgroup.mem_sup_left y.2)
      have hE9ab : IsElemAbelian p
          (Subgroup.zpowers x ⊔ Subgroup.zpowers (y : MulAut W)) := by
        apply IsElemAbelian.sup_of_commute
        · exact isElemAbelian_zpowers hxp
        · exact isElemAbelian_zpowers hyp
        · intro a ha b hb
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
          exact (hycent.zpow_zpow i j).eq
      have hE9X : Subgroup.zpowers x ⊔ Subgroup.zpowers (y : MulAut W) ≤ X :=
        sup_le (Subgroup.zpowers_le.mpr hxX) (Subgroup.zpowers_le.mpr (F.le_x y.2))
      have hE9fix : ∀ e ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers (y : MulAut W),
          e (t w) = t w := by
        intro e he
        have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers (y : MulAut W) ≤
            MulAction.stabilizer (MulAut W) (t w) := by
          apply sup_le
          · rw [Subgroup.zpowers_le]
            exact MulAction.mem_stabilizer_iff.mpr
              (by simpa using mem_centSub.mp hxcU' (t w) hw'U')
          · rw [Subgroup.zpowers_le]
            exact MulAction.mem_stabilizer_iff.mpr
              (by simpa using F.fix_u' (y : MulAut W) y.2 (t w) hw'U')
        exact MulAction.mem_stabilizer_iff.mp (hle he)
      have hbadE9 := hbadw' _ hE9X hE9ab hE9fix
      have hxnot : x ∉ Subgroup.zpowers (y : MulAut W) := by
        intro hxmem
        have hxL : x ∈ L := (Subgroup.zpowers_le.mpr y.2) hxmem
        exact hx1 (hcen x hxL (fun b hb => hxcomm b (Subgroup.mem_sup_left hb)))
      have hlt : Subgroup.zpowers (y : MulAut W) <
          Subgroup.zpowers x ⊔ Subgroup.zpowers (y : MulAut W) := by
        refine lt_of_le_of_ne le_sup_right ?_
        intro heq
        exact hxnot (heq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩))
      have hcardFy : Nat.card ↥(Subgroup.zpowers (y : MulAut W)) = p := by
        rw [Nat.card_zpowers, Subgroup.orderOf_coe, hyord]
      have hplt : p < Nat.card ↥
          (Subgroup.zpowers x ⊔ Subgroup.zpowers (y : MulAut W)) := by
        rw [← hcardFy]
        exact Subgroup.card_lt_of_lt hlt
      omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
