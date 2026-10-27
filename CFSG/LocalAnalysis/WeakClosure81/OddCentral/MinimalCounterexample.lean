module
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.Combined
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.HyperplaneNormal
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open Subgroup

section
variable {G M : Type*} [Group G] [Finite G] [AddCommGroup M] [Finite M] [DistribMulAction G M]

theorem frame_facts {d : Fin 3 → G} {t : G} (hd : ∀ i, d i * d i = 1)
    (hdc : ∀ i j, d i * d j = d j * d i) (hdn : ∀ i j, i ≠ j → d i ≠ d j)
    (ht : ∀ i, t * d i * t⁻¹ = d (i + 1)) {c : G} (hcdef : c = d 0 * d 1 * d 2)
    {z : Fin 3 → G} (hzdef : ∀ a, z a = d (a + 1) * d (a + 2)) :
    c * c = 1 ∧ (∀ a, z a * z a = 1) ∧ z 2 = z 0 * z 1 ∧ (∀ a, c * z a = z a * c) ∧
      z 0 * z 1 = z 1 * z 0 ∧ z 0 ≠ 1 ∧ z 1 ≠ 1 ∧ z 0 ≠ z 1 ∧
      (∀ a, t * z a * t⁻¹ = z (a + 1)) ∧ t * c = c * t ∧ d 0 = c * z 0 ∧
      z 0 = d 1 * d 2 ∧ z 1 = d 2 * d 0 := by
  have hdc' : ∀ i j, Commute (d i) (d j) := hdc
  have hdinv : ∀ i, (d i)⁻¹ = d i := fun i => inv_eq_of_mul_eq_one_right (hd i)
  have hz0 : z 0 = d 1 * d 2 := hzdef 0
  have hz1 : z 1 = d 2 * d 0 := hzdef 1
  have hz2' : z 2 = d 0 * d 1 := hzdef 2
  have hcd : ∀ i, Commute c (d i) := fun i => by
    rw [hcdef]; exact ((hdc' 0 i).mul_left (hdc' 1 i)).mul_left (hdc' 2 i)
  have hcomm2 : ∀ i j k l, Commute (d i * d j) (d k * d l) := fun i j k l =>
    ((hdc' i k).mul_right (hdc' i l)).mul_left ((hdc' j k).mul_right (hdc' j l))
  have hc : c * c = 1 := by
    rw [hcdef]
    exact mul_sq_eq_one (mul_sq_eq_one (hd 0) (hd 1) (hdc 0 1)) (hd 2)
      ((hdc' 0 2).mul_left (hdc' 1 2))
  have hz : ∀ a, z a * z a = 1 := fun a => by rw [hzdef]; exact mul_sq_eq_one (hd _) (hd _) (hdc _ _)
  have hz2 : z 2 = z 0 * z 1 := by
    rw [hz0, hz1, hz2', show d 1 * d 2 * (d 2 * d 0) = d 1 * (d 2 * d 2) * d 0 by group, hd 2,
      mul_one, hdc 1 0]
  have hcz : ∀ a, c * z a = z a * c := fun a => by rw [hzdef]; exact ((hcd _).mul_right (hcd _)).eq
  have h01 : z 0 * z 1 = z 1 * z 0 := by rw [hz0, hz1]; exact (hcomm2 _ _ _ _).eq
  have hne : ∀ i j, i ≠ j → d i * d j ≠ 1 := fun i j hij h => hdn i j hij (by
    rw [← hdinv j]; exact eq_inv_of_mul_eq_one_left h)
  have hn0 : z 0 ≠ 1 := by rw [hz0]; exact hne 1 2 (by decide)
  have hn1 : z 1 ≠ 1 := by rw [hz1]; exact hne 2 0 (by decide)
  have hn01 : z 0 ≠ z 1 := by
    rw [hz0, hz1, hdc 2 0]
    intro h
    exact hdn 1 0 (by decide) (mul_right_cancel h)
  have htz : ∀ a, t * z a * t⁻¹ = z (a + 1) := by
    intro a
    rw [hzdef, hzdef, show t * (d (a + 1) * d (a + 2)) * t⁻¹ =
      (t * d (a + 1) * t⁻¹) * (t * d (a + 2) * t⁻¹) by group, ht, ht, add_right_comm a 2 1]
  have htc : t * c = c * t := by
    have h : t * c * t⁻¹ = c := by
      rw [hcdef, show t * (d 0 * d 1 * d 2) * t⁻¹ =
        (t * d 0 * t⁻¹) * (t * d 1 * t⁻¹) * (t * d 2 * t⁻¹) by group, ht, ht, ht]
      show d 1 * d 2 * d 0 = d 0 * d 1 * d 2
      rw [mul_assoc, hdc 2 0, ← mul_assoc, hdc 1 0]
    calc t * c = t * c * t⁻¹ * t := by group
      _ = c * t := by rw [h]
  have hd0 : d 0 = c * z 0 := by
    rw [hcdef, hz0, show d 0 * d 1 * d 2 * (d 1 * d 2) = d 0 * d 1 * (d 2 * d 1) * d 2 by group,
      hdc 2 1, show d 0 * d 1 * (d 1 * d 2) * d 2 = d 0 * (d 1 * d 1) * (d 2 * d 2) by group,
      hd 1, hd 2, mul_one, mul_one]
  exact ⟨hc, hz, hz2, hcz, h01, hn0, hn1, hn01, htz, htc, hd0, hz0, hz1⟩

theorem la_frame (hModd : Odd (Nat.card M)) {d : Fin 3 → G} {t : G} (hd : ∀ i, d i * d i = 1)
    (hdc : ∀ i j, d i * d j = d j * d i) (hdn : ∀ i j, i ≠ j → d i ≠ d j)
    (ht : ∀ i, t * d i * t⁻¹ = d (i + 1))
    (hLAM : ∀ i j, i ≠ j → ∀ m : M, (d i * d j) • m = m → d i • m = m) {c : G}
    (hcdef : c = d 0 * d 1 * d 2) {z : Fin 3 → G} (hzdef : ∀ a, z a = d (a + 1) * d (a + 2)) :
    ∀ m : M, ∀ a, c • m = m → z a • m = -m → m = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, htz, htc, hd0, hz0, -⟩ := frame_facts hd hdc hdn ht hcdef hzdef
  have hLA0 : ∀ m : M, c • m = m → z 0 • m = -m → m = 0 := by
    intro m hcm hzm
    have hx : d 0 • m = -m := by rw [hd0, mul_smul, hzm, smul_neg, hcm]
    rw [hz0] at hzm
    exact eq_zero_of_LA hModd (hd 1) (hdc 0 1) (hdc 1 2) (hLAM 0 1 (by decide))
      (hLAM 0 2 (by decide)) hx hzm
  have hrot : ∀ a, (∀ m : M, c • m = m → z a • m = -m → m = 0) →
      ∀ m : M, c • m = m → z (a + 1) • m = -m → m = 0 := by
    intro a ih m hcm hzm
    have h1 : c • t⁻¹ • m = t⁻¹ • m := by
      rw [smul_smul, show c * t⁻¹ = t⁻¹ * c by
        calc c * t⁻¹ = t⁻¹ * (t * c) * t⁻¹ := by group
          _ = t⁻¹ * (c * t) * t⁻¹ := by rw [htc]
          _ = t⁻¹ * c := by group, mul_smul, hcm]
    have h2 : z a • t⁻¹ • m = -(t⁻¹ • m) := by
      rw [smul_smul, show z a * t⁻¹ = t⁻¹ * z (a + 1) by rw [← htz]; group, mul_smul, hzm,
        smul_neg]
    have := ih _ h1 h2
    simpa using congrArg (t • ·) this
  intro m a
  have key : ∀ a : Fin 3, a = 0 ∨ a = 0 + 1 ∨ a = 0 + 1 + 1 := by decide
  rcases key a with rfl | rfl | rfl
  · exact hLA0 m
  · exact hrot 0 hLA0 m
  · exact hrot _ (hrot 0 hLA0) m

theorem exists_hyperplane {r : ℕ} (hr : r.Prime) (hrM : ¬ r ∣ Nat.card M) {V : Subgroup G}
    (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hVr : ∀ v ∈ V, v ^ r = 1) (hV1 : V ≠ ⊥)
    (hMnt : ∃ m : M, m ≠ 0) :
    ∃ H : Subgroup G, H ≤ V ∧ H ≠ V ∧ (∀ K : Subgroup G, H ≤ K → K ≤ V → K = H ∨ K = V) ∧
      ∃ x : M, x ≠ 0 ∧ ∀ h ∈ H, h • x = x := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  letI iC : CommGroup V :=
    { (inferInstance : Group V) with
      mul_comm := fun a b => Subtype.ext (hVab a a.2 b b.2) }
  haveI : CFSG.IsElementaryAbelian r V :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hVab a a.2 b b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by simpa using hVr g g.2) }
  haveI : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).mpr hV1
  let α : V →* MulAut (Multiplicative M) :=
    { toFun := fun a =>
        { toFun := fun x => Multiplicative.ofAdd ((a : G) • x.toAdd)
          invFun := fun x => Multiplicative.ofAdd ((a : G)⁻¹ • x.toAdd)
          left_inv := fun x => by simp
          right_inv := fun x => by simp
          map_mul' := fun x x' => by simp [smul_add] }
      map_one' := by ext x; simp
      map_mul' := fun a b => by ext x; simp [mul_smul] }
  have hgen := CFSG.SolvableSignalizer.iSup_fixedBySubgroup_index_eq_top r hr α
    (by rwa [show Nat.card (Multiplicative M) = Nat.card M from
      Nat.card_congr Multiplicative.toAdd])
  obtain ⟨m₀, hm₀⟩ := hMnt
  have hex : ∃ B : Subgroup V, B.index = r ∧
      ∃ x ∈ CFSG.SolvableSignalizer.fixedBySubgroup α B, x ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hle : (⨆ (B : Subgroup V) (_ : B.index = r),
        CFSG.SolvableSignalizer.fixedBySubgroup α B) ≤ ⊥ :=
      iSup₂_le fun B hB x hx => (Subgroup.mem_bot).mpr (hcon B hB x hx)
    rw [hgen] at hle
    have := hle (Subgroup.mem_top (Multiplicative.ofAdd m₀))
    rw [Subgroup.mem_bot] at this
    exact hm₀ (by simpa using congrArg Multiplicative.toAdd this)
  obtain ⟨B, hB, y, hy, hy1⟩ := hex
  have hyfix : ∀ b ∈ B, (b : G) • y.toAdd = y.toAdd := fun b hb =>
    congrArg Multiplicative.toAdd
      ((CFSG.SolvableSignalizer.mem_fixedBySubgroup α B y).mp hy b hb)
  have hyne : y.toAdd ≠ 0 := fun h => hy1 (by simpa using congrArg Multiplicative.ofAdd h)
  have hcoat : IsCoatom B := Subgroup.isCoatom_of_index_prime (by rw [hB]; exact hr)
  refine ⟨B.map V.subtype, map_subtype_le B, ?_, ?_, y.toAdd, hyne, ?_⟩
  · intro hBV
    apply hcoat.1
    rw [eq_top_iff]
    intro v _
    have : (v : G) ∈ B.map V.subtype := by rw [hBV]; exact v.2
    obtain ⟨b, hb, hbv⟩ := this
    have : b = v := Subtype.ext hbv
    rwa [← this]
  · intro K hHK hKV
    have hBK : B ≤ K.subgroupOf V := fun b hb => by
      rw [mem_subgroupOf]; exact hHK (mem_map_of_mem _ hb)
    rcases (hcoat.le_iff.mp hBK) with h | h
    · right
      refine le_antisymm hKV fun v hv => ?_
      have : (⟨v, hv⟩ : V) ∈ K.subgroupOf V := by rw [h]; exact mem_top _
      exact this
    · left
      refine le_antisymm (fun k hk => ?_) hHK
      have : (⟨k, hKV hk⟩ : V) ∈ K.subgroupOf V := hk
      rw [h] at this
      exact mem_map_of_mem V.subtype this
  · rintro _ ⟨b, hb, rfl⟩
    exact hyfix b hb


theorem false_of_propS_counterexample {r : ℕ} (hr : r.Prime) (hrM : ¬ r ∣ Nat.card M)
    (hModd : Odd (Nat.card M))
    (hfaith : ∀ g : G, (∀ m : M, g • m = m) → g = 1)
    (hirr : ∀ N : AddSubgroup M, (∀ g : G, ∀ m ∈ N, g • m ∈ N) → N = ⊥ ∨ N = ⊤)
    {Q Q₀ R : Subgroup G} [hQn : Q.Normal] [hRn : R.Normal] (hQ₀Q : Q₀ ≤ Q)
    (hQodd : Odd (Nat.card Q)) (hQ' : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Q₀)
    (hQ₀Z : Q₀ ≤ center G) (hQ₀p : IsPGroup r Q₀) (hQr : ∀ x ∈ Q, x ^ r ∈ Q₀)
    (hchief : ∀ N : Subgroup G, N.Normal → Q₀ ≤ N → N ≤ Q → N = Q₀ ∨ N = Q)
    (hRodd : Odd (Nat.card R))
    {d : Fin 3 → G} {t : G} (hd : ∀ i, d i * d i = 1) (hdc : ∀ i j, d i * d j = d j * d i)
    (hdn : ∀ i j, i ≠ j → d i ≠ d j) (ht : ∀ i, t * d i * t⁻¹ = d (i + 1))
    (hcR : ∀ g : G, (d 0 * d 1 * d 2)⁻¹ * (g * (d 0 * d 1 * d 2) * g⁻¹) ∈ R)
    (hRc : ∀ y ∈ R, ∀ x ∈ Q, (y * (d 0 * d 1 * d 2) * y⁻¹ * (d 0 * d 1 * d 2)⁻¹) * x *
      (y * (d 0 * d 1 * d 2) * y⁻¹ * (d 0 * d 1 * d 2)⁻¹)⁻¹ * x⁻¹ ∈ Q₀)
    (hLAW : ∀ i j, i ≠ j → ∀ x ∈ Q, (d i * d j) * x * (d i * d j)⁻¹ * x⁻¹ ∈ Q₀ →
      d i * x * (d i)⁻¹ * x⁻¹ ∈ Q₀)
    (hLAM : ∀ i j, i ≠ j → ∀ m : M, (d i * d j) • m = m → d i • m = m)
    (hS1 : ∃ x ∈ Q, d 0 * x * (d 0)⁻¹ * x⁻¹ ∉ Q₀)
    (hgen : normalClosure ({d 0} : Set G) = ⊤) : False := by
  classical
  haveI hQ₀n : Q₀.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_center_iff.mp (hQ₀Z hn) g, mul_inv_cancel_right]; exact hn⟩
  have hQ₀c : ∀ q ∈ Q₀, ∀ g : G, g * q * g⁻¹ = q := fun q hq g => by
    rw [Subgroup.mem_center_iff.mp (hQ₀Z hq) g, mul_inv_cancel_right]
  obtain ⟨hcQ, hT₁, hrg⟩ := s3_prime (R := R) hQ₀Q hQodd hQ' hchief hRodd hd hdc hcR hRc hLAW hS1
  have hconjQ : ∀ g : G, ∀ x ∈ Q, g⁻¹ * x * g ∈ Q := fun g x hx => by
    simpa using hQn.conj_mem x hx g⁻¹
  let R₁ : Subgroup G :=
    { carrier := {y | y ∈ R ∧ ∀ x ∈ Q, y * x * y⁻¹ * x⁻¹ ∈ Q₀}
      mul_mem' := fun {a b} ha hb => ⟨R.mul_mem ha.1 hb.1, fun x hx => by
        have h1 := hb.2 x hx
        have h2 := ha.2 x hx
        rw [show a * b * x * (a * b)⁻¹ * x⁻¹ =
          a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) by group, hQ₀c _ h1 a]
        exact Q₀.mul_mem h1 h2⟩
      one_mem' := ⟨R.one_mem, fun x _ => by simp⟩
      inv_mem' := fun {a} ha => ⟨R.inv_mem ha.1, fun x hx => by
        have h := Q₀.inv_mem (ha.2 _ (hconjQ a x hx))
        convert h using 1
        group⟩ }
  haveI hR₁n : R₁.Normal := ⟨fun y hy g => ⟨hRn.conj_mem y hy.1 g, fun x hx => by
    have := hQ₀n.conj_mem _ (hy.2 _ (hconjQ g x hx)) g
    convert this using 1
    group⟩⟩
  have hR₁odd : Odd (Nat.card R₁) :=
    Odd.of_dvd_nat hRodd (Subgroup.card_dvd_of_le (fun y hy => hy.1))
  obtain ⟨hQab, hcent⟩ := centralizes_of_s3_frame (R₁ := R₁) hr hrM hModd hfaith hirr hQ₀Q hQodd
    hQ' hQ₀Z hQ₀p hQr hchief hRodd hR₁odd (fun y hy => hy.2) hd hdc hdn ht hcR hRc hLAW hLAM hS1
  obtain ⟨c, hcdef⟩ : ∃ c, c = d 0 * d 1 * d 2 := ⟨_, rfl⟩
  let z : Fin 3 → G := fun a => d (a + 1) * d (a + 2)
  obtain ⟨hc, hz, hz2, hcz, h01, -, -, -, htz, -, hd0, hz0, hz1⟩ :=
    frame_facts hd hdc hdn ht hcdef (z := z) (fun _ => rfl)
  have hLA := la_frame hModd hd hdc hdn ht hLAM hcdef (z := z) (fun _ => rfl)
  rw [← hcdef] at hcQ hrg hcR
  have hrQ : ∀ g : G, ∀ x ∈ Q, (c⁻¹ * (g * c * g⁻¹)) * x * (c⁻¹ * (g * c * g⁻¹))⁻¹ = x :=
    fun g x hx => hcent _ ⟨hcR g, fun x hx => hrg g x hx⟩ x hx
  let V : Subgroup G :=
    { carrier := {x | x ∈ Q ∧ c * x * c⁻¹ = x⁻¹}
      mul_mem' := fun {a b} ha hb => ⟨Q.mul_mem ha.1 hb.1, by
        rw [show c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) by group, ha.2, hb.2,
          mul_inv_rev]
        exact hQab _ (Q.inv_mem ha.1) _ (Q.inv_mem hb.1)⟩
      one_mem' := ⟨Q.one_mem, by simp⟩
      inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, by
        rw [show c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ by group, ha.2]⟩ }
  haveI hVn : V.Normal := ⟨fun v hv g => ⟨hQn.conj_mem v hv.1 g, by
    have hr' := hrQ g⁻¹ v hv.1
    calc c * (g * v * g⁻¹) * c⁻¹
        = g * (c * ((c⁻¹ * (g⁻¹ * c * g⁻¹⁻¹)) * v * (c⁻¹ * (g⁻¹ * c * g⁻¹⁻¹))⁻¹) * c⁻¹) * g⁻¹ := by
          group
      _ = g * (c * v * c⁻¹) * g⁻¹ := by rw [hr']
      _ = (g * v * g⁻¹)⁻¹ := by rw [hv.2]; group⟩⟩
  have hVQ₀ : ∀ v ∈ V, v ∈ Q₀ → v = 1 := by
    intro v hv hv0
    have h : v = v⁻¹ := by have := hv.2; rwa [hQ₀c v hv0 c] at this
    have : v * v = 1 := by nth_rewrite 2 [h]; exact mul_inv_cancel v
    exact eq_one_of_mul_self hQodd hv.1 this
  have hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw => hQab v hv.1 w hw.1
  have hVodd : Odd (Nat.card V) :=
    Odd.of_dvd_nat hQodd (Subgroup.card_dvd_of_le (fun x hx => hx.1))
  have hVr : ∀ v ∈ V, v ^ r = 1 := fun v hv =>
    hVQ₀ _ ⟨pow_mem hv.1 r, by rw [← conj_pow, hv.2, inv_pow]⟩ (hQr v hv.1)
  haveI : Fact r.Prime := ⟨hr⟩
  have hVp : IsPGroup r V := fun v => ⟨1, Subtype.ext (by simpa using hVr v v.2)⟩
  have hcop : Nat.Coprime (Nat.card V) (Nat.card M) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hVp
    rw [hk]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hr).mpr hrM)
  have hV1 : V ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx, hnot⟩ := hS1
    apply hnot
    have hy : x * (c * x * c⁻¹)⁻¹ ∈ V := ⟨Q.mul_mem hx (Q.inv_mem (hQn.conj_mem x hx c)), by
      rw [show c * (x * (c * x * c⁻¹)⁻¹) * c⁻¹ = (c * x * c⁻¹) * ((c * c) * x * (c * c)⁻¹)⁻¹ by
        group, hc]
      group⟩
    rw [hbot, mem_bot, mul_inv_eq_one] at hy
    have hx2 : x * x ∈ Q₀ := by
      have := hcQ x hx
      rwa [← hy] at this
    have hxQ₀ := mem_of_sq_mem hQodd hx hx2
    rw [hQ₀c x hxQ₀, mul_inv_cancel]
    exact Q₀.one_mem
  have hM0 : ∀ m : M, (∀ v ∈ V, v • m = m) → m = 0 := by
    let N : AddSubgroup M :=
      { carrier := {m | ∀ v ∈ V, v • m = m}
        add_mem' := fun {a b} ha hb v hv => by rw [smul_add, ha v hv, hb v hv]
        zero_mem' := fun v _ => smul_zero v
        neg_mem' := fun {a} ha v hv => by rw [smul_neg, ha v hv] }
    have hinv : ∀ g : G, ∀ m ∈ N, g • m ∈ N := by
      intro g m hm v hv
      have := hm _ (by simpa using hVn.conj_mem v hv g⁻¹)
      calc v • g • m = g • ((g⁻¹ * v * g) • m) := by
            rw [← mul_smul, ← mul_smul]; congr 1; group
        _ = g • m := by rw [this]
    intro m hm
    rcases hirr N hinv with h | h
    · have : m ∈ N := hm
      rw [h] at this
      exact (AddSubgroup.mem_bot).mp this
    · exfalso
      apply hV1
      rw [eq_bot_iff]
      intro v hv
      rw [mem_bot]
      exact hfaith v fun m' => by
        have : m' ∈ N := by rw [h]; exact AddSubgroup.mem_top m'
        exact this v hv
  have hMnt : ∃ m : M, m ≠ 0 := by
    by_contra h
    push_neg at h
    apply hV1
    rw [eq_bot_iff]
    intro v _
    rw [mem_bot]
    exact hfaith v fun m => by rw [h m, smul_zero]
  obtain ⟨H, hHV, hHV', hHmax, x, hx0, hxH⟩ := exists_hyperplane hr hrM hVab hVr hV1 hMnt
  have hT : ∀ v ∈ V, z 0 * v * (z 0)⁻¹ = v → z 1 * v * (z 1)⁻¹ = v → v = 1 :=
    fun v hv h0 h1 => hVQ₀ v hv (hT₁ v hv.1 (by rw [← hz0, h0, mul_inv_cancel]; exact Q₀.one_mem)
      (by rw [← hz1, h1, mul_inv_cancel]; exact Q₀.one_mem))
  have hgen' : normalClosure ({c * z 0} : Set G) = ⊤ := by rw [← hd0]; exact hgen
  exact false_of_frame_hyperplane hcop hModd hVab hVodd hHV hHmax hHV' hM0 hxH hx0 hc hz hz2 hcz
    h01 (fun v hv => hv.2) hT hLA htz hgen'

end

end CFSG.LocalAnalysis.WeakClosure81.OddCentral

