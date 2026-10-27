module

public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreFrame

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open scoped commutatorElement Pointwise

variable {Q : Type*} [Group Q] [Finite Q]

private lemma seven_eight_core_braid_eq_one_of_sq_eq_one {H : Subgroup Q} {x : Q}
    (hodd : Odd (Nat.card H)) (hx : x ∈ H) (h2 : x ^ 2 = 1) : x = 1 := by
  have hdvd : orderOf x ∣ Nat.card H := Subgroup.orderOf_dvd_natCard H hx
  have hodd' : Odd (orderOf x) := Odd.of_dvd_nat hodd hdvd
  have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ hodd') (Nat.not_odd_iff_even.mpr (by decide))

private lemma seven_eight_core_braid_closure_comm_involutions {S : Set Q} {c : Q}
    (hS1 : ∀ x ∈ S, x * x = 1) (hSc : ∀ x ∈ S, c * x = x * c)
    (hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    (∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x) ∧
      (∀ g ∈ Subgroup.closure S, g * g = 1) ∧
      (∀ g ∈ Subgroup.closure S, c * g = g * c) := by
  have hSK : S ⊆ Subgroup.centralizer (Subgroup.closure S : Set Q) := by
    intro s hs
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem t ht => exact (hScomm s hs t ht).symm
    | one => simp
    | mul x y hx hy ihx ihy => rw [mul_assoc, ihy, ← mul_assoc, ihx, mul_assoc]
    | inv x hx ih =>
        exact (show Commute x s from ih).inv_left
  have hKcomm : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp ((Subgroup.closure_le _).mpr hSK hx) y hy).symm
  refine ⟨hKcomm, ?_, ?_⟩
  · intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hS1 x hx
    | one => simp
    | mul x y hx hy ihx ihy =>
        calc (x * y) * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [hKcomm y hy x hx]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [ihx, ihy, mul_one]
    | inv x hx ih => rw [inv_eq_of_mul_eq_one_right ih, ih]
  · intro g hg
    have h : Subgroup.closure S ≤ Subgroup.centralizer {c} := by
      refine (Subgroup.closure_le _).mpr ?_
      intro s hs
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hSc s hs
    exact Subgroup.mem_centralizer_iff.mp (h hg) c (Set.mem_singleton c)

private lemma seven_eight_core_braid_choose_two_gt {n : ℕ} (hn : 4 ≤ n) : n < n.choose 2 := by
  rw [Nat.choose_two_right]
  refine (Nat.lt_div_iff_mul_lt (k := 2) (by decide)).mpr ?_
  have hge : 2 * n + 2 ≤ n * (n - 1) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
    rw [hm]
    have hsub : 4 + m - 1 = m + 3 := by
      rw [show 4 + m = m + 3 + 1 by ring, Nat.add_sub_cancel]
    rw [hsub]
    calc 2 * (4 + m) + 2 = 2 * m + 10 := by ring
      _ ≤ 2 * m + 10 + (m * m + 5 * m + 2) := Nat.le_add_right _ _
      _ = (4 + m) * (m + 3) := by ring
  have h1 : 2 * n + 1 < n * (n - 1) := Nat.lt_of_succ_le hge
  have h2 : 2 * n < n * (n - 1) - 1 := Nat.lt_sub_iff_add_lt.mpr h1
  simpa [Nat.mul_comm] using h2

private lemma seven_eight_core_braid_eq_inv_of_pow_three {s m : Q} (h3 : s ^ 3 = 1)
    (hm : s * m * s⁻¹ = m⁻¹) : m = m⁻¹ := by
  have hmid : s * m⁻¹ * s⁻¹ = m := by
    have h : (s * m * s⁻¹)⁻¹ = m := by rw [hm]; group
    rwa [show (s * m * s⁻¹)⁻¹ = s * m⁻¹ * s⁻¹ by group] at h
  have h2 : s ^ 3 * m * (s ^ 3)⁻¹ = m⁻¹ := by
    calc s ^ 3 * m * (s ^ 3)⁻¹
        = s ^ 2 * (s * m * s⁻¹) * (s ^ 2)⁻¹ := by group
      _ = s ^ 2 * m⁻¹ * (s ^ 2)⁻¹ := by rw [hm]
      _ = s * (s * m⁻¹ * s⁻¹) * s⁻¹ := by rw [pow_two]; group
      _ = s * m * s⁻¹ := by rw [hmid]
      _ = m⁻¹ := hm
  have h1 : s ^ 3 * m * (s ^ 3)⁻¹ = m := by rw [h3]; group
  exact h1.symm.trans h2

theorem commutator_zpowers_le_iSup_of_pow_three {Xb : Subgroup Q} (hodd : Odd (Nat.card Xb))
    {ι : Type*} (a : ι → Q) (hinv : ∀ i, a i * a i = 1) (hcomm : ∀ i j, a i * a j = a j * a i)
    (hnorm : ∀ i, a i ∈ Subgroup.normalizer (Xb : Set Q))
    (hcent : ∀ i j, i ≠ j → ∀ m ∈ ⁅Xb, Subgroup.zpowers (a j)⁆, a i * m = m * a i)
    (hab : ∀ i, ∀ m ∈ ⁅Xb, Subgroup.zpowers (a i)⁆, ∀ m' ∈ ⁅Xb, Subgroup.zpowers (a i)⁆,
      m * m' = m' * m)
    {b : Q} (hb : b * b = 1) (hbX : b ∈ Subgroup.normalizer (Xb : Set Q))
    (hbab : ∀ m ∈ ⁅Xb, Subgroup.zpowers b⁆, ∀ m' ∈ ⁅Xb, Subgroup.zpowers b⁆, m * m' = m' * m)
    {i : ι} (hi : (a i * b) ^ 3 = 1) {f : Q} (hf : f ∈ Subgroup.closure (a '' {j | j ≠ i}))
    (hfb : a i * f * b = b * (a i * f)) :
    ⁅Xb, Subgroup.zpowers b⁆ ≤ ⨆ j, ⁅Xb, Subgroup.zpowers (a j)⁆ := by
  let M : ι → Subgroup Q := fun j => ⁅Xb, Subgroup.zpowers (a j)⁆
  let U : Subgroup Q := ⨆ j, M j
  change ⁅Xb, Subgroup.zpowers b⁆ ≤ U
  have hRleXb : ⁅Xb, Subgroup.zpowers b⁆ ≤ Xb := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.le_normalizer_iff_commutator_le_right).mp (Subgroup.zpowers_le.mpr hbX)
  have hoddR : Odd (Nat.card (⁅Xb, Subgroup.zpowers b⁆ : Subgroup Q)) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hRleXb)
  have hfS1 : ∀ x ∈ a '' {j | j ≠ i}, x * x = 1 := by
    rintro x ⟨j, _, rfl⟩
    exact hinv j
  have hfSc : ∀ x ∈ a '' {j | j ≠ i}, a i * x = x * a i := by
    rintro x ⟨j, _, rfl⟩
    exact hcomm i j
  have hfScomm : ∀ x ∈ a '' {j | j ≠ i}, ∀ y ∈ a '' {j | j ≠ i}, x * y = y * x := by
    rintro x ⟨j, _, rfl⟩ y ⟨l, _, rfl⟩
    exact hcomm j l
  obtain ⟨-, hfinv, hfc⟩ :=
    seven_eight_core_braid_closure_comm_involutions hfS1 hfSc hfScomm
  have hf2 : f * f = 1 := hfinv f hf
  have haif : a i * f = f * a i := hfc f hf
  have hfcent : ∀ m ∈ M i, f * m = m * f := by
    have hmem : f ∈ Subgroup.centralizer (M i : Set Q) := by
      refine (Subgroup.closure_le _).mpr ?_ hf
      rintro x ⟨j, hj, rfl⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro m hm
      have hm' : m ∈ ⁅Xb, Subgroup.zpowers (a i)⁆ := hm
      exact (hcent j i hj m hm').symm
    intro m hm
    exact (Subgroup.mem_centralizer_iff.mp hmem m hm).symm
  have he2 : (a i * f) * (a i * f) = 1 := by
    calc (a i * f) * (a i * f) = a i * (f * a i) * f := by group
      _ = a i * (a i * f) * f := by rw [← haif]
      _ = (a i * a i) * (f * f) := by group
      _ = 1 := by rw [hinv i, hf2, mul_one]
  have hfX : f ∈ Subgroup.normalizer (Xb : Set Q) := by
    refine (Subgroup.closure_le _).mpr ?_ hf
    rintro x ⟨j, _, rfl⟩
    exact hnorm j
  have heX : a i * f ∈ Subgroup.normalizer (Xb : Set Q) :=
    (Subgroup.normalizer (Xb : Set Q)).mul_mem (hnorm i) hfX
  have hconjb : (MulAut.conj (a i * f)) b = b := by
    show (a i * f) * b * (a i * f)⁻¹ = b
    calc (a i * f) * b * (a i * f)⁻¹ = b * (a i * f) * (a i * f)⁻¹ := by rw [hfb]
      _ = b := by group
  have hzpj : (Subgroup.zpowers b).map (MulAut.conj (a i * f)) = Subgroup.zpowers b := by
    rw [MonoidHom.map_zpowers]
    show Subgroup.zpowers ((MulAut.conj (a i * f)) b) = Subgroup.zpowers b
    rw [hconjb]
  have heR : a i * f ∈ Subgroup.normalizer (⁅Xb, Subgroup.zpowers b⁆ : Subgroup Q) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp heX, hzpj]
  have hCR : ∀ x ∈ ⁅Xb, Subgroup.zpowers b⁆, (a i * f) * x = x * (a i * f) → x = 1 := by
    intro x hx hxcomm
    have hxXb : x ∈ Xb := hRleXb hx
    have hax : a i * x = x * a i :=
      commute_of_mul_commute hodd (hinv i) (hnorm i) haif (hab i) hfcent x hxXb hxcomm
    have hbx : b * x * b⁻¹ = x⁻¹ :=
      conj_eq_inv_of_mem_commutator_zpowers hb hbab x hx
    have hsx : (a i * b) * x * (a i * b)⁻¹ = x⁻¹ := by
      calc (a i * b) * x * (a i * b)⁻¹
          = a i * (b * x * b⁻¹) * (a i)⁻¹ := by group
        _ = a i * x⁻¹ * (a i)⁻¹ := by rw [hbx]
        _ = x⁻¹ := by
              calc a i * x⁻¹ * (a i)⁻¹ = (a i * x * (a i)⁻¹)⁻¹ := by group
                _ = x⁻¹ := by rw [hax]; group
    have hx_inv : x = x⁻¹ := seven_eight_core_braid_eq_inv_of_pow_three hi hsx
    have hx2 : x ^ 2 = 1 := by
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.mpr hx_inv
    exact seven_eight_core_braid_eq_one_of_sq_eq_one hoddR hx hx2
  have hRle : ⁅Xb, Subgroup.zpowers b⁆ ≤
      ⁅⁅Xb, Subgroup.zpowers b⁆, Subgroup.zpowers (a i * f)⁆ := by
    intro x hx
    have hRre : ⁅⁅Xb, Subgroup.zpowers b⁆, Subgroup.zpowers (a i * f)⁆ ≤
        ⁅Xb, Subgroup.zpowers b⁆ := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.le_normalizer_iff_commutator_le_right).mp (Subgroup.zpowers_le.mpr heR)
    obtain ⟨m, hm, cc, hcc, hccomm, hxmc⟩ :=
      exists_mul_eq_of_commutator_zpowers hoddR he2 heR
        (fun m hm m' hm' => hbab m (hRre hm) m' (hRre hm')) x hx
    have hcc1 : cc = 1 := hCR cc hcc hccomm
    rw [hcc1, mul_one] at hxmc
    rw [hxmc]
    exact hm
  have hnormM : ∀ j k, a j ∈ Subgroup.normalizer (M k : Set Q) := by
    intro j k
    by_cases hjk : j = k
    · rw [hjk]
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      show (⁅Xb, Subgroup.zpowers (a k)⁆).map (MulAut.conj (a k)) = ⁅Xb, Subgroup.zpowers (a k)⁆
      have hzp : (Subgroup.zpowers (a k)).map (MulAut.conj (a k)) = Subgroup.zpowers (a k) := by
        rw [MonoidHom.map_zpowers]
        show Subgroup.zpowers ((MulAut.conj (a k)) (a k)) = Subgroup.zpowers (a k)
        rw [MulAut.conj_apply, hinv k, one_mul]
        exact Subgroup.zpowers_inv
      rw [Subgroup.map_commutator, (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hnorm k), hzp]
    · refine Subgroup.centralizer_le_normalizer (M k : Set Q) ?_
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro m hm
      have hm' : m ∈ ⁅Xb, Subgroup.zpowers (a k)⁆ := hm
      exact (hcent j k hjk m hm').symm
  have hnormU : ∀ j, a j ∈ Subgroup.normalizer (U : Set Q) := by
    intro j
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show (⨆ k, M k).map (MulAut.conj (a j)) = ⨆ k, M k
    rw [Subgroup.map_iSup]
    exact iSup_congr (fun k => (Subgroup.mem_normalizer_iff_map_conj_eq).mp (hnormM j k))
  have hmain : ∀ g ∈ Subgroup.closure (Set.range a),
      g ∈ Subgroup.normalizer (U : Set Q) ∧ ∀ x ∈ Xb, ⁅x, g⁆ ∈ U := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact ⟨hnormU j, fun x hx =>
          le_iSup M j (commutator_mem_commutator hx (Subgroup.mem_zpowers (a j)))⟩
    | one => exact ⟨(Subgroup.normalizer (U : Set Q)).one_mem,
        by intro x hx; simp [commutatorElement_def]⟩
    | mul y z hy hz ihy ihz =>
        refine ⟨(Subgroup.normalizer (U : Set Q)).mul_mem ihy.1 ihz.1, fun x hx => ?_⟩
        rw [show ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) by
              simp only [commutatorElement_def]; group]
        exact U.mul_mem (ihy.2 x hx)
          ((Subgroup.mem_normalizer_iff.mp ihy.1 (⁅x, z⁆)).mp (ihz.2 x hx))
    | inv y hy ihy =>
        refine ⟨(Subgroup.normalizer (U : Set Q)).inv_mem ihy.1, fun x hx => ?_⟩
        rw [show ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y by
              simp only [commutatorElement_def]; group]
        have hmem := (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (U : Set Q)).inv_mem ihy.1) (⁅x, y⁆⁻¹)).mp
          (U.inv_mem (ihy.2 x hx))
        simpa only [inv_inv] using hmem
  have he_mem : a i * f ∈ Subgroup.closure (Set.range a) := by
    refine (Subgroup.closure (Set.range a)).mul_mem (Subgroup.subset_closure ⟨i, rfl⟩) ?_
    exact Subgroup.closure_mono (by rintro x ⟨j, _, rfl⟩; exact ⟨j, rfl⟩) hf
  have heU : ⁅Xb, Subgroup.zpowers (a i * f)⁆ ≤ U := by
    refine Subgroup.commutator_le.mpr (fun x hx g hg => ?_)
    exact (hmain g (Subgroup.zpowers_le.mpr he_mem hg)).2 x hx
  exact hRle.trans ((Subgroup.commutator_mono hRleXb le_rfl).trans heU)

theorem exists_mul_commute_of_ncard_le {ι : Type*} [Finite ι] (hι : 4 ≤ Nat.card ι) (a : ι → Q)
    (hcomm : ∀ i j, a i * a j = a j * a i) (b : Q) {S : Set Q} (hS : S.ncard ≤ Nat.card ι)
    (hmem : ∀ i j, i ≠ j → (a i * a j)⁻¹ * b * (a i * a j) ∈ S) :
    ∃ i, ∃ f ∈ Subgroup.closure (a '' {j | j ≠ i}), a i * f * b = b * (a i * f) := by
  classical
  letI := Fintype.ofFinite ι
  let xOf (p : Finset ι) (h : p.card = 2) : ι := Classical.choose (Finset.card_eq_two.mp h)
  let yOf (p : Finset ι) (h : p.card = 2) : ι :=
    Classical.choose (Classical.choose_spec (Finset.card_eq_two.mp h))
  let g : Finset ι → Q := fun p =>
    if h : p.card = 2 then
      (a (xOf p h) * a (yOf p h))⁻¹ * b * (a (xOf p h) * a (yOf p h))
    else b
  let P : Finset (Finset ι) := Finset.powersetCard 2 Finset.univ
  have hcards : P.card = (Nat.card ι).choose 2 := by
    show (Finset.powersetCard 2 Finset.univ).card = (Nat.card ι).choose 2
    rw [Finset.card_powersetCard, Finset.card_univ, Nat.card_eq_fintype_card]
  have hlt : Nat.card ι < (Nat.card ι).choose 2 := seven_eight_core_braid_choose_two_gt hι
  have hcardP : (P : Set (Finset ι)).ncard = (Nat.card ι).choose 2 := by
    rw [Set.ncard_coe_finset, hcards]
  have hlt' : S.ncard < (P : Set (Finset ι)).ncard := by
    rw [hcardP]
    exact lt_of_le_of_lt hS hlt
  have hgen : ∀ i, ∀ z, z ≠ i → a z ∈ Subgroup.closure (a '' {w | w ≠ i}) := by
    intro i z hz
    exact Subgroup.subset_closure (Set.mem_image_of_mem a (show z ∈ {w | w ≠ i} from hz))
  have hmemP : ∀ r ∈ (P : Set (Finset ι)), g r ∈ S := by
    intro r hr
    have hr2 : r.card = 2 := (Finset.mem_powersetCard.mp hr).2
    have hspec := Classical.choose_spec (Classical.choose_spec (Finset.card_eq_two.mp hr2))
    have hgr : g r = (a (xOf r hr2) * a (yOf r hr2))⁻¹ * b *
        (a (xOf r hr2) * a (yOf r hr2)) := by
      dsimp only [g]
      rw [dif_pos hr2]
    rw [hgr]
    exact hmem (xOf r hr2) (yOf r hr2) hspec.1
  obtain ⟨p, hp, q, hq, hpq, hgp⟩ :=
    Set.exists_ne_map_eq_of_ncard_lt_of_maps_to hlt' hmemP
  have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp hp).2
  have hq2 : q.card = 2 := (Finset.mem_powersetCard.mp hq).2
  have hpspec := Classical.choose_spec (Classical.choose_spec (Finset.card_eq_two.mp hp2))
  have hqspec := Classical.choose_spec (Classical.choose_spec (Finset.card_eq_two.mp hq2))
  have hp_eq : p = {xOf p hp2, yOf p hp2} := hpspec.2
  have hxy : xOf p hp2 ≠ yOf p hp2 := hpspec.1
  have hq_eq : q = {xOf q hq2, yOf q hq2} := hqspec.2
  have hkq : xOf q hq2 ∈ q := by
    have hmem : xOf q hq2 ∈ ({xOf q hq2, yOf q hq2} : Finset ι) := Finset.mem_insert_self _ _
    rwa [← hqspec.2] at hmem
  have hlq : yOf q hq2 ∈ q := by
    have hmem : yOf q hq2 ∈ ({xOf q hq2, yOf q hq2} : Finset ι) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rwa [← hqspec.2] at hmem
  have hE : (a (xOf p hp2) * a (yOf p hp2))⁻¹ * b * (a (xOf p hp2) * a (yOf p hp2))
      = (a (xOf q hq2) * a (yOf q hq2))⁻¹ * b
        * (a (xOf q hq2) * a (yOf q hq2)) := by
    have h := hgp
    dsimp only [g] at h
    rw [dif_pos hp2, dif_pos hq2] at h
    exact h
  have hcomm_b : (a (xOf p hp2) * a (yOf p hp2)) * (a (xOf q hq2) * a (yOf q hq2))⁻¹ * b
      = b * ((a (xOf p hp2) * a (yOf p hp2)) * (a (xOf q hq2) * a (yOf q hq2))⁻¹) := by
    let X : Q := a (xOf p hp2) * a (yOf p hp2)
    let Y : Q := a (xOf q hq2) * a (yOf q hq2)
    have hE' : X⁻¹ * b * X = Y⁻¹ * b * Y := hE
    change X * Y⁻¹ * b = b * (X * Y⁻¹)
    have h1 : b * X = X * Y⁻¹ * b * Y := by
      calc b * X = X * (X⁻¹ * b * X) := by group
        _ = X * (Y⁻¹ * b * Y) := by rw [hE']
        _ = X * Y⁻¹ * b * Y := by group
    have h2 : b * X * Y⁻¹ = X * Y⁻¹ * b := by
      calc b * X * Y⁻¹ = (X * Y⁻¹ * b * Y) * Y⁻¹ := by rw [h1]
        _ = X * Y⁻¹ * b := by group
    calc (X * Y⁻¹) * b = X * Y⁻¹ * b := rfl
      _ = b * X * Y⁻¹ := h2.symm
      _ = b * (X * Y⁻¹) := by group
  by_cases hxq : xOf p hp2 ∈ q
  · have hyq : yOf p hp2 ∉ q := by
      intro hyq
      have hsub : p ⊆ q := by
        rw [hp_eq]
        intro z hz
        rw [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hxq
        · exact hyq
      exact hpq (Finset.eq_of_subset_of_card_le hsub (by simp [hp2, hq2]))
    have hky : xOf q hq2 ≠ yOf p hp2 := fun h => hyq (by rw [← h]; exact hkq)
    have hly : yOf q hq2 ≠ yOf p hp2 := fun h => hyq (by rw [← h]; exact hlq)
    refine ⟨yOf p hp2, a (xOf p hp2) * (a (xOf q hq2) * a (yOf q hq2))⁻¹, ?_, ?_⟩
    · exact (Subgroup.closure (a '' {w | w ≠ yOf p hp2})).mul_mem
        (hgen (yOf p hp2) (xOf p hp2) hxy)
        ((Subgroup.closure (a '' {w | w ≠ yOf p hp2})).inv_mem
          ((Subgroup.closure (a '' {w | w ≠ yOf p hp2})).mul_mem
            (hgen (yOf p hp2) (xOf q hq2) hky)
            (hgen (yOf p hp2) (yOf q hq2) hly)))
    · have hswap : a (yOf p hp2) * (a (xOf p hp2) * (a (xOf q hq2) * a (yOf q hq2))⁻¹)
            = (a (xOf p hp2) * a (yOf p hp2))
              * (a (xOf q hq2) * a (yOf q hq2))⁻¹ := by
        rw [← mul_assoc, hcomm (yOf p hp2) (xOf p hp2)]
      rw [hswap]
      exact hcomm_b
  · have hkx : xOf q hq2 ≠ xOf p hp2 := fun h => hxq (by rw [← h]; exact hkq)
    have hlx : yOf q hq2 ≠ xOf p hp2 := fun h => hxq (by rw [← h]; exact hlq)
    have hyx : yOf p hp2 ≠ xOf p hp2 := fun h => hxy h.symm
    refine ⟨xOf p hp2, a (yOf p hp2) * (a (xOf q hq2) * a (yOf q hq2))⁻¹, ?_, ?_⟩
    · exact (Subgroup.closure (a '' {w | w ≠ xOf p hp2})).mul_mem
        (hgen (xOf p hp2) (yOf p hp2) hyx)
        ((Subgroup.closure (a '' {w | w ≠ xOf p hp2})).inv_mem
          ((Subgroup.closure (a '' {w | w ≠ xOf p hp2})).mul_mem
            (hgen (xOf p hp2) (xOf q hq2) hkx)
            (hgen (xOf p hp2) (yOf q hq2) hlx)))
    · have hid : a (xOf p hp2) * (a (yOf p hp2) * (a (xOf q hq2) * a (yOf q hq2))⁻¹)
            = (a (xOf p hp2) * a (yOf p hp2))
              * (a (xOf q hq2) * a (yOf q hq2))⁻¹ := by
        group
      rw [hid]
      exact hcomm_b

theorem false_of_map_conj_eq {Xb : Subgroup Q} (hodd : Odd (Nat.card Xb)) {ι : Type*}
    (a : ι → Q) (hinv : ∀ i, a i * a i = 1) (hnorm : ∀ i, a i ∈ Subgroup.normalizer (Xb : Set Q))
    (hcent : ∀ i j, i ≠ j → ∀ m ∈ ⁅Xb, Subgroup.zpowers (a j)⁆, a i * m = m * a i)
    (hab : ∀ i, ∀ m ∈ ⁅Xb, Subgroup.zpowers (a i)⁆, ∀ m' ∈ ⁅Xb, Subgroup.zpowers (a i)⁆,
      m * m' = m' * m)
    {b : Q} (hb : b * b = 1) (hb3 : ∀ i, (a i * b) ^ 3 = 1) {k l : ι}
    (hmap : (⨆ j, ⨆ (_ : j ≠ k), ⁅Xb, Subgroup.zpowers (a j)⁆).map (MulAut.conj b).toMonoidHom =
      ⨆ j, ⨆ (_ : j ≠ l), ⁅Xb, Subgroup.zpowers (a j)⁆)
    {j : ι} (hjk : j ≠ k) (hjl : j ≠ l) (hne : ⁅Xb, Subgroup.zpowers (a j)⁆ ≠ ⊥) : False := by
  let M : ι → Subgroup Q := fun x => ⁅Xb, Subgroup.zpowers (a x)⁆
  let Ck : Subgroup Q := ⨆ x, ⨆ (_ : x ≠ k), M x
  let Cl : Subgroup Q := ⨆ x, ⨆ (_ : x ≠ l), M x
  have hmap' : Ck.map (MulAut.conj b).toMonoidHom = Cl := hmap
  have hMleXb : ∀ x, M x ≤ Xb := by
    intro x
    show ⁅Xb, Subgroup.zpowers (a x)⁆ ≤ Xb
    rw [Subgroup.commutator_comm]
    exact (Subgroup.le_normalizer_iff_commutator_le_right).mp (Subgroup.zpowers_le.mpr (hnorm x))
  have hoddM : ∀ x, Odd (Nat.card (M x)) := fun x =>
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le (hMleXb x))
  have hak_cent_Ck : ∀ y ∈ Ck, a k * y = y * a k := by
    intro y hy
    refine Subgroup.iSup_induction (C := fun w => a k * w = w * a k)
      (fun x => ⨆ (_ : x ≠ k), M x) hy ?_ ?_ ?_
    · intro i z hz
      refine Subgroup.iSup_induction (C := fun w => a k * w = w * a k)
        (fun (_ : i ≠ k) => M i) hz ?_ ?_ ?_
      · intro hik m hm
        have hm' : m ∈ ⁅Xb, Subgroup.zpowers (a i)⁆ := hm
        exact hcent k i hik.symm m hm'
      · simp
      · intro u v hu hv
        calc a k * (u * v) = (a k * u) * v := by rw [mul_assoc]
          _ = (u * a k) * v := by rw [hu]
          _ = u * (a k * v) := by rw [mul_assoc]
          _ = u * (v * a k) := by rw [hv]
          _ = (u * v) * a k := by rw [mul_assoc]
    · simp
    · intro u v hu hv
      calc a k * (u * v) = (a k * u) * v := by rw [mul_assoc]
        _ = (u * a k) * v := by rw [hu]
        _ = u * (a k * v) := by rw [mul_assoc]
        _ = u * (v * a k) := by rw [hv]
        _ = (u * v) * a k := by rw [mul_assoc]
  set c : Q := b * a k * b⁻¹ with hc
  have hc_cent : ∀ z ∈ Cl, c * z * c⁻¹ = z := by
    intro z hz
    have hz' : z ∈ Ck.map (MulAut.conj b).toMonoidHom := by rw [hmap']; exact hz
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz'
    have hyz' : b * y * b⁻¹ = z := hyz
    rw [← hyz']
    have haky : a k * y = y * a k := hak_cent_Ck y hy
    have haky' : a k * y * (a k)⁻¹ = y := by
      calc a k * y * (a k)⁻¹ = y * a k * (a k)⁻¹ := by rw [haky]
        _ = y := by group
    rw [hc]
    calc (b * a k * b⁻¹) * (b * y * b⁻¹) * (b * a k * b⁻¹)⁻¹
        = b * (a k * y * (a k)⁻¹) * b⁻¹ := by group
      _ = b * y * b⁻¹ := by rw [haky']
  have hb_inv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hkey : a k * b * a k * b * a k * b = 1 := by
    have hs := hb3 k
    rw [show (a k * b) ^ 3 = a k * b * a k * b * a k * b by
          rw [pow_three']; simp only [mul_assoc]] at hs
    exact hs
  have hmain : a k * b * a k * b * a k = b := by
    have h := congrArg (· * b) hkey
    rw [one_mul] at h
    have hXX : a k * b * a k * b * a k = ((a k * b * a k * b * a k) * b) * b := by
      conv_rhs => rw [mul_assoc, hb, mul_one]
    exact hXX.trans h
  have hb_eq : b = a k * c * a k := by
    rw [hc, hb_inv]
    calc b = a k * b * a k * b * a k := hmain.symm
      _ = a k * (b * a k * b) * a k := by group
  have hm1 : ∀ m ∈ M j, m = 1 := by
    intro m hm
    have hmCl : m ∈ Cl :=
      le_iSup (fun x => ⨆ (_ : x ≠ l), M x) j (le_iSup (fun _ : j ≠ l => M j) hjl hm)
    have hcm : c * m * c⁻¹ = m := hc_cent m hmCl
    have hbm : b * m * b⁻¹ = m := by
      rw [hb_eq]
      have hakm : a k * m = m * a k := by
        have hm' : m ∈ ⁅Xb, Subgroup.zpowers (a j)⁆ := hm
        exact hcent k j hjk.symm m hm'
      have hakm' : a k * m * (a k)⁻¹ = m := by
        calc a k * m * (a k)⁻¹ = m * a k * (a k)⁻¹ := by rw [hakm]
          _ = m := by group
      calc (a k * c * a k) * m * (a k * c * a k)⁻¹
          = a k * c * (a k * m * (a k)⁻¹) * c⁻¹ * (a k)⁻¹ := by group
        _ = a k * c * m * c⁻¹ * (a k)⁻¹ := by rw [hakm']
        _ = a k * (c * m * c⁻¹) * (a k)⁻¹ := by group
        _ = a k * m * (a k)⁻¹ := by rw [hcm]
        _ = m := hakm'
    have hajm : a j * m * (a j)⁻¹ = m⁻¹ := by
      have hm' : m ∈ ⁅Xb, Subgroup.zpowers (a j)⁆ := hm
      exact conj_eq_inv_of_mem_commutator_zpowers (hinv j) (hab j) m hm'
    have hsm : (a j * b) * m * (a j * b)⁻¹ = m⁻¹ := by
      calc (a j * b) * m * (a j * b)⁻¹
          = a j * (b * m * b⁻¹) * (a j)⁻¹ := by group
        _ = a j * m * (a j)⁻¹ := by rw [hbm]
        _ = m⁻¹ := hajm
    have hm_inv : m = m⁻¹ := seven_eight_core_braid_eq_inv_of_pow_three (hb3 j) hsm
    have hm2 : m ^ 2 = 1 := by
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.mpr hm_inv
    exact seven_eight_core_braid_eq_one_of_sq_eq_one (hoddM j) hm hm2
  exact hne ((Subgroup.eq_bot_iff_forall (M j)).mpr hm1)

end CFSG.LocalAnalysis.WeakClosure81
