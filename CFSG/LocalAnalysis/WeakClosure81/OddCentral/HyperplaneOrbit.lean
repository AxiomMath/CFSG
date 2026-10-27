module
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.QAbelian
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open Subgroup

section
variable {G M : Type*} [Group G] [Finite G] [AddCommGroup M] [Finite M] [DistribMulAction G M]

theorem nsmul_ne_zero_of_coprime {n : ℕ} (hn : Nat.Coprime n (Nat.card M)) {m : M}
    (hm : m ≠ 0) : n • m ≠ 0 := by
  intro h
  have h1 : addOrderOf m ∣ n := addOrderOf_dvd_of_nsmul_eq_zero h
  have h2 : addOrderOf m ∣ Nat.card M := addOrderOf_dvd_natCard m
  exact hm (AddMonoid.addOrderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hn h1 h2))

theorem sum_smul_fix (H : Subgroup G) [Fintype H] {g : G} (hg : g ∈ H) (m : M) :
    g • ∑ h : H, (h : G) • m = ∑ h : H, (h : G) • m := by
  rw [Finset.smul_sum]
  simp_rw [smul_smul]
  exact Equiv.sum_comp (Equiv.mulLeft (⟨g, hg⟩ : H)) (fun h : H => (h : G) • m)

theorem sum_smul_const (H : Subgroup G) [Fintype H] {m : M} (hm : ∀ h ∈ H, h • m = m) :
    ∑ h : H, (h : G) • m = Nat.card H • m := by
  rw [Finset.sum_congr rfl (fun (h : H) _ => hm (h : G) h.2), Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card]

private theorem sum_smul_eq_zero {V H : Subgroup G} [Fintype H]
    (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hHV : H ≤ V)
    (hHmax : ∀ K : Subgroup G, H ≤ K → K ≤ V → K = H ∨ K = V) {M₁ : AddSubgroup M}
    (hM₁V : ∀ v ∈ V, ∀ m ∈ M₁, v • m ∈ M₁) (hM₁0 : ∀ m ∈ M₁, (∀ v ∈ V, v • m = m) → m = 0)
    {z : G} (hzV : ∀ v ∈ V, z * v * z⁻¹ ∈ V) (hzN : ¬ ∀ h ∈ H, z * h * z⁻¹ ∈ H) {m : M}
    (hm : m ∈ M₁) (hmC : ∀ h ∈ H, (z * h * z⁻¹) • m = m) : ∑ h : H, (h : G) • m = 0 := by
  set S := ∑ h : H, (h : G) • m with hS
  have hSM : S ∈ M₁ := AddSubgroup.sum_mem _ fun h _ => hM₁V h (hHV h.2) m hm
  let K : Subgroup G := MulAction.stabilizer G S ⊓ V
  have hHK : H ≤ K := fun h hh => ⟨(MulAction.mem_stabilizer_iff).mpr (sum_smul_fix H hh m), hHV hh⟩
  rcases hHmax K hHK inf_le_right with hK | hK
  · exfalso
    apply hzN
    intro h hh
    have hzh : z * h * z⁻¹ ∈ V := hzV h (hHV hh)
    have : z * h * z⁻¹ ∈ K := by
      refine ⟨(MulAction.mem_stabilizer_iff).mpr ?_, hzh⟩
      rw [hS, Finset.smul_sum]
      refine Finset.sum_congr rfl fun h' _ => ?_
      rw [smul_smul, hVab _ hzh _ (hHV h'.2), ← smul_smul, hmC h hh]
    rwa [hK] at this
  · exact hM₁0 S hSM fun v hv => (MulAction.mem_stabilizer_iff).mp (hK ▸ hv : v ∈ K).1

private theorem plus_or_minus {V H : Subgroup G} (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v)
    (hVodd : Odd (Nat.card V)) (hHV : H ≤ V)
    (hHmax : ∀ K : Subgroup G, H ≤ K → K ≤ V → K = H ∨ K = V) (hHV' : H ≠ V) {z : G}
    (hz : z * z = 1) (hzV : ∀ v ∈ V, z * v * z⁻¹ ∈ V) (hzN : ∀ h ∈ H, z * h * z⁻¹ ∈ H) :
    (∀ v ∈ V, z * v * z⁻¹ * v⁻¹ ∈ H) ∨ (∀ v ∈ V, z * v * z⁻¹ * v ∈ H) := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  let Cp : Subgroup G :=
    { carrier := {v | v ∈ V ∧ z * v * z⁻¹ * v⁻¹ ∈ H}
      mul_mem' := fun {v w} hv hw => by
        refine ⟨V.mul_mem hv.1 hw.1, ?_⟩
        have hzw := hzV w hw.1
        have e1 : z * (v * w) * z⁻¹ * (v * w)⁻¹ =
            (z * v * z⁻¹ * v⁻¹) * (v * (z * w * z⁻¹ * w⁻¹) * v⁻¹) := by group
        have e2 : v * (z * w * z⁻¹ * w⁻¹) * v⁻¹ = z * w * z⁻¹ * w⁻¹ := by
          rw [hVab v hv.1 _ (V.mul_mem hzw (V.inv_mem hw.1))]; group
        rw [e1, e2]
        exact H.mul_mem hv.2 hw.2
      one_mem' := ⟨V.one_mem, by simp⟩
      inv_mem' := fun {v} hv => by
        refine ⟨V.inv_mem hv.1, ?_⟩
        have hzv := hzV v hv.1
        have : z * v⁻¹ * z⁻¹ * v⁻¹⁻¹ = (z * v * z⁻¹ * v⁻¹)⁻¹ := by
          have hc := hVab v hv.1 _ (V.inv_mem hzv)
          calc z * v⁻¹ * z⁻¹ * v⁻¹⁻¹ = (z * v * z⁻¹)⁻¹ * v := by group
            _ = v * (z * v * z⁻¹)⁻¹ := (hc).symm
            _ = (z * v * z⁻¹ * v⁻¹)⁻¹ := by group
        rw [this]; exact H.inv_mem hv.2 }
  let Cm : Subgroup G :=
    { carrier := {v | v ∈ V ∧ z * v * z⁻¹ * v ∈ H}
      mul_mem' := fun {v w} hv hw => by
        refine ⟨V.mul_mem hv.1 hw.1, ?_⟩
        have hzw := hzV w hw.1
        have e1 : z * (v * w) * z⁻¹ * (v * w) =
            (z * v * z⁻¹) * ((z * w * z⁻¹) * v) * w := by group
        rw [e1, ← hVab v hv.1 _ hzw, show z * v * z⁻¹ * (v * (z * w * z⁻¹)) * w =
          (z * v * z⁻¹ * v) * (z * w * z⁻¹ * w) by group]
        exact H.mul_mem hv.2 hw.2
      one_mem' := ⟨V.one_mem, by simp⟩
      inv_mem' := fun {v} hv => by
        refine ⟨V.inv_mem hv.1, ?_⟩
        have hzv := hzV v hv.1
        have : z * v⁻¹ * z⁻¹ * v⁻¹ = (z * v * z⁻¹ * v)⁻¹ := by
          have hc := hVab v hv.1 _ (V.inv_mem hzv)
          calc z * v⁻¹ * z⁻¹ * v⁻¹ = (z * v * z⁻¹)⁻¹ * v⁻¹ := by group
            _ = (v * (z * v * z⁻¹))⁻¹ := by group
            _ = (z * v * z⁻¹ * v)⁻¹ := by rw [hVab v hv.1 _ hzv]
        rw [this]; exact H.inv_mem hv.2 }
  have hHp : H ≤ Cp := fun h hh => ⟨hHV hh, H.mul_mem (hzN h hh) (H.inv_mem hh)⟩
  have hHm : H ≤ Cm := fun h hh => ⟨hHV hh, H.mul_mem (hzN h hh) hh⟩
  rcases hHmax Cp hHp (fun v hv => hv.1) with hp | hp
  · rcases hHmax Cm hHm (fun v hv => hv.1) with hm | hm
    · exfalso
      obtain ⟨v, hvV, hvH⟩ : ∃ v ∈ V, v ∉ H := by
        by_contra hcon
        push Not at hcon
        exact hHV' (le_antisymm hHV hcon)
      have hzv := hzV v hvV
      have ha : v * (z * v * z⁻¹) ∈ Cp := by
        refine ⟨V.mul_mem hvV hzv, ?_⟩
        have : z * (v * (z * v * z⁻¹)) * z⁻¹ * (v * (z * v * z⁻¹))⁻¹ = 1 := by
          have e : z * (v * (z * v * z⁻¹)) * z⁻¹ = (z * v * z⁻¹) * v := by
            rw [show z * (v * (z * v * z⁻¹)) * z⁻¹ = (z * v * z⁻¹) * ((z * z) * v * (z⁻¹ * z⁻¹))
              by group, hz, ← mul_inv_rev, hz]; group
          rw [e, hVab _ hzv v hvV, mul_inv_cancel]
        rw [this]; exact H.one_mem
      have hb : v * (z * v * z⁻¹)⁻¹ ∈ Cm := by
        refine ⟨V.mul_mem hvV (V.inv_mem hzv), ?_⟩
        have : z * (v * (z * v * z⁻¹)⁻¹) * z⁻¹ * (v * (z * v * z⁻¹)⁻¹) = 1 := by
          have e : z * (v * (z * v * z⁻¹)⁻¹) * z⁻¹ = (z * v * z⁻¹) * v⁻¹ := by
            rw [show z * (v * (z * v * z⁻¹)⁻¹) * z⁻¹ =
              (z * v * z⁻¹) * ((z * z) * v⁻¹ * (z⁻¹ * z⁻¹)) by group, hz, ← mul_inv_rev, hz]
            group
          rw [e, show z * v * z⁻¹ * v⁻¹ * (v * (z * v * z⁻¹)⁻¹) = 1 by group]
        rw [this]; exact H.one_mem
      rw [hp] at ha
      rw [hm] at hb
      have hsq : v ^ 2 ∈ H := by
        have := H.mul_mem ha hb
        rwa [show v * (z * v * z⁻¹) * (v * (z * v * z⁻¹)⁻¹) = v * v by
          rw [← mul_assoc, mul_assoc v, hVab _ hzv v hvV]; group, ← sq] at this
      obtain ⟨k, hk⟩ := exists_pow_sq hVodd hvV
      exact hvH (hk ▸ H.pow_mem hsq k)
    · exact Or.inr fun v hv => (hm ▸ hv : v ∈ Cm).2
  · exact Or.inl fun v hv => (hp ▸ hv : v ∈ Cp).2

private theorem minus_mul_minus {V H : Subgroup G} (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v)
    (hHV : H ≤ V) {u w : G} (huV : ∀ v ∈ V, u * v * u⁻¹ ∈ V) (hwV : ∀ v ∈ V, w * v * w⁻¹ ∈ V)
    (huN : ∀ h ∈ H, u * h * u⁻¹ ∈ H) (hwN : ∀ h ∈ H, w * h * w⁻¹ ∈ H)
    (hu : ∀ v ∈ V, u * v * u⁻¹ * v ∈ H) (hw : ∀ v ∈ V, w * v * w⁻¹ * v ∈ H) :
    (∀ h ∈ H, (u * w) * h * (u * w)⁻¹ ∈ H) ∧ ∀ v ∈ V, (u * w) * v * (u * w)⁻¹ * v⁻¹ ∈ H := by
  refine ⟨fun h hh => ?_, fun v hv => ?_⟩
  · rw [show (u * w) * h * (u * w)⁻¹ = u * (w * h * w⁻¹) * u⁻¹ by group]
    exact huN _ (hwN h hh)
  · set a := w * v * w⁻¹ * v with ha
    have haH : a ∈ H := hw v hv
    have hwv : w * v * w⁻¹ = a * v⁻¹ := by rw [ha]; group
    have hb := hu v⁻¹ (V.inv_mem hv)
    have e : (u * w) * v * (u * w)⁻¹ * v⁻¹ =
        (u * a * u⁻¹) * (u * v⁻¹ * u⁻¹ * v⁻¹) := by
      rw [show (u * w) * v * (u * w)⁻¹ = u * (w * v * w⁻¹) * u⁻¹ by group, hwv]; group
    rw [e]
    exact H.mul_mem (huN a haH) hb

private theorem false_of_plus {V H : Subgroup G} [Fintype H]
    (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hHV : H ≤ V)
    (hHmax : ∀ K : Subgroup G, H ≤ K → K ≤ V → K = H ∨ K = V) {M₁ : AddSubgroup M}
    (hM₁V : ∀ v ∈ V, ∀ m ∈ M₁, v • m ∈ M₁) (hM₁0 : ∀ m ∈ M₁, (∀ v ∈ V, v • m = m) → m = 0)
    {c z z' : G} (hz : z * z = 1) (hz' : z' * z' = 1) (hzz' : z * z' = z' * z)
    (hcz : c * z = z * c) (hcz' : c * z' = z' * c)
    (hz'V : ∀ v ∈ V, z' * v * z'⁻¹ ∈ V) (hzz'V : ∀ v ∈ V, (z * z') * v * (z * z')⁻¹ ∈ V)
    (hz'N : ¬ ∀ h ∈ H, z' * h * z'⁻¹ ∈ H) (hzz'N : ¬ ∀ h ∈ H, (z * z') * h * (z * z')⁻¹ ∈ H)
    (hLA : ∀ y : M, c • y = y → z' • y = -y → y = 0)
    {x : M} (hx : x ∈ M₁) (hxH : ∀ h ∈ H, h • x = x) (hxc : c • x = x)
    (hM₁z' : z' • x ∈ M₁) (hM₁zz' : (z * z') • x ∈ M₁)
    (hs : ∑ h : H, (h : G) • (x + z • x) ≠ 0) : False := by
  have hz'C : ∀ h ∈ H, (z' * h * z'⁻¹) • (z' • x) = z' • x := fun h hh => by
    rw [smul_smul, show z' * h * z'⁻¹ * z' = z' * h by group, ← smul_smul, hxH h hh]
  have hzz'C : ∀ h ∈ H, ((z * z') * h * (z * z')⁻¹) • ((z * z') • x) = (z * z') • x :=
    fun h hh => by
      rw [smul_smul, show (z * z') * h * (z * z')⁻¹ * (z * z') = (z * z') * h by group,
        ← smul_smul, hxH h hh]
  have h0 := sum_smul_eq_zero hVab hHV hHmax hM₁V hM₁0 hz'V hz'N hM₁z' hz'C
  have h0' := sum_smul_eq_zero hVab hHV hHmax hM₁V hM₁0 hzz'V hzz'N hM₁zz' hzz'C
  set y := x + z • x - z' • x - (z * z') • x with hy
  have hyc : c • y = y := by
    rw [hy, smul_sub, smul_sub, smul_add, hxc, smul_smul, hcz, ← smul_smul, hxc, smul_smul c z',
      hcz', ← smul_smul, hxc, smul_smul c (z * z'), ← mul_assoc, hcz, mul_assoc, hcz',
      ← mul_assoc, ← smul_smul, hxc]
  have hyz' : z' • y = -y := by
    rw [hy, smul_sub, smul_sub, smul_add, smul_smul, smul_smul, smul_smul, hz',
      one_smul, show z' * (z * z') = z by rw [← mul_assoc, ← hzz', mul_assoc, hz', mul_one],
      ← hzz']
    abel
  have hy0 := hLA y hyc hyz'
  apply hs
  have : ∑ h : H, (h : G) • y = ∑ h : H, (h : G) • (x + z • x) := by
    rw [hy]
    simp_rw [smul_sub, Finset.sum_sub_distrib, h0, h0', sub_zero]
  rw [← this, hy0]
  simp

private theorem false_of_minus {V H : Subgroup G} [Fintype H]
    (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hHV : H ≤ V)
    (hHmax : ∀ K : Subgroup G, H ≤ K → K ≤ V → K = H ∨ K = V) {M₁ : AddSubgroup M}
    (hM₁V : ∀ v ∈ V, ∀ m ∈ M₁, v • m ∈ M₁) (hM₁0 : ∀ m ∈ M₁, (∀ v ∈ V, v • m = m) → m = 0)
    {c z z' : G} (hz : z * z = 1) (hz' : z' * z' = 1) (hzz' : z * z' = z' * z)
    (hcz : c * z = z * c) (hcz' : c * z' = z' * c)
    (hz'V : ∀ v ∈ V, z' * v * z'⁻¹ ∈ V) (hzz'V : ∀ v ∈ V, (z * z') * v * (z * z')⁻¹ ∈ V)
    (hz'N : ¬ ∀ h ∈ H, z' * h * z'⁻¹ ∈ H) (hzz'N : ¬ ∀ h ∈ H, (z * z') * h * (z * z')⁻¹ ∈ H)
    (hLA : ∀ y : M, c • y = y → z' • y = -y → y = 0)
    {x : M} (hx : x ∈ M₁) (hxH : ∀ h ∈ H, h • x = x) (hxc : c • x = x)
    (hM₁z' : z' • x ∈ M₁) (hM₁zz' : (z * z') • x ∈ M₁)
    (hs : ∑ h : H, (h : G) • (x - z • x) ≠ 0) : False := by
  have hz'C : ∀ h ∈ H, (z' * h * z'⁻¹) • (z' • x) = z' • x := fun h hh => by
    rw [smul_smul, show z' * h * z'⁻¹ * z' = z' * h by group, ← smul_smul, hxH h hh]
  have hzz'C : ∀ h ∈ H, ((z * z') * h * (z * z')⁻¹) • ((z * z') • x) = (z * z') • x :=
    fun h hh => by
      rw [smul_smul, show (z * z') * h * (z * z')⁻¹ * (z * z') = (z * z') * h by group,
        ← smul_smul, hxH h hh]
  have h0 := sum_smul_eq_zero hVab hHV hHmax hM₁V hM₁0 hz'V hz'N hM₁z' hz'C
  have h0' := sum_smul_eq_zero hVab hHV hHmax hM₁V hM₁0 hzz'V hzz'N hM₁zz' hzz'C
  set y := x - z • x - z' • x + (z * z') • x with hy
  have hyc : c • y = y := by
    rw [hy, smul_add, smul_sub, smul_sub, hxc, smul_smul, hcz, ← smul_smul, hxc, smul_smul c z',
      hcz', ← smul_smul, hxc, smul_smul c (z * z'), ← mul_assoc, hcz, mul_assoc, hcz',
      ← mul_assoc, ← smul_smul, hxc]
  have hyz' : z' • y = -y := by
    rw [hy, smul_add, smul_sub, smul_sub, smul_smul, smul_smul, smul_smul, hz',
      one_smul, show z' * (z * z') = z by rw [← mul_assoc, ← hzz', mul_assoc, hz', mul_one],
      ← hzz']
    abel
  have hy0 := hLA y hyc hyz'
  apply hs
  have : ∑ h : H, (h : G) • y = ∑ h : H, (h : G) • (x - z • x) := by
    rw [hy]
    simp_rw [smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, h0, h0',
      sub_zero, add_zero]
  rw [← this, hy0]
  simp

private theorem false_of_normalizing {V H : Subgroup G} [Fintype H]
    (hcop : Nat.Coprime (2 * Nat.card H) (Nat.card M))
    (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hHV : H ≤ V)
    (hHmax : ∀ K : Subgroup G, H ≤ K → K ≤ V → K = H ∨ K = V) {M₁ : AddSubgroup M}
    (hM₁V : ∀ v ∈ V, ∀ m ∈ M₁, v • m ∈ M₁) (hM₁0 : ∀ m ∈ M₁, (∀ v ∈ V, v • m = m) → m = 0)
    {c z z' : G} (hz : z * z = 1) (hz' : z' * z' = 1) (hzz' : z * z' = z' * z)
    (hcz : c * z = z * c) (hcz' : c * z' = z' * c)
    (hz'V : ∀ v ∈ V, z' * v * z'⁻¹ ∈ V) (hzz'V : ∀ v ∈ V, (z * z') * v * (z * z')⁻¹ ∈ V)
    (hzN : ∀ h ∈ H, z * h * z⁻¹ ∈ H)
    (hz'N : ¬ ∀ h ∈ H, z' * h * z'⁻¹ ∈ H) (hzz'N : ¬ ∀ h ∈ H, (z * z') * h * (z * z')⁻¹ ∈ H)
    (hLA : ∀ y : M, c • y = y → z' • y = -y → y = 0)
    (hM₁z : ∀ m ∈ M₁, z • m ∈ M₁) (hM₁z' : ∀ m ∈ M₁, z' • m ∈ M₁)
    {x : M} (hx : x ∈ M₁) (hxH : ∀ h ∈ H, h • x = x) (hxc : c • x = x) (hx0 : x ≠ 0) : False := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hzxH : ∀ h ∈ H, h • (z • x) = z • x := fun h hh => by
    have := hzN h hh
    rw [smul_smul, show h * z = z * (z * h * z⁻¹) by rw [hzi, ← mul_assoc, ← mul_assoc, hz, one_mul], ← smul_smul, hxH _ this]
  have hzxc : c • (z • x) = z • x := by rw [smul_smul, hcz, ← smul_smul, hxc]
  have hM₁zz' : ∀ m ∈ M₁, (z * z') • m ∈ M₁ := fun m hm => by
    rw [← smul_smul]; exact hM₁z _ (hM₁z' m hm)
  have hsum : ∀ y : M, y ∈ M₁ → (∀ h ∈ H, h • y = y) → y ≠ 0 →
      ∑ h : H, (h : G) • (y + y) ≠ 0 := by
    intro y _ hyH hy0
    rw [sum_smul_const H (fun h hh => by rw [smul_add, hyH h hh]), ← two_nsmul, smul_smul,
      mul_comm]
    exact nsmul_ne_zero_of_coprime hcop hy0
  by_cases hp : x + z • x = 0
  · have hzx : z • x = -x := eq_neg_of_add_eq_zero_right hp
    refine false_of_minus hVab hHV hHmax hM₁V hM₁0 hz hz' hzz' hcz hcz' hz'V hzz'V hz'N hzz'N
      hLA hx hxH hxc (hM₁z' x hx) (hM₁zz' x hx) ?_
    rw [hzx, sub_neg_eq_add]
    exact hsum x hx hxH hx0
  · set y := x + z • x with hy
    have hyM : y ∈ M₁ := M₁.add_mem hx (hM₁z x hx)
    have hyH : ∀ h ∈ H, h • y = y := fun h hh => by rw [hy, smul_add, hxH h hh, hzxH h hh]
    have hyc : c • y = y := by rw [hy, smul_add, hxc, hzxc]
    have hzy : z • y = y := by rw [hy, smul_add, smul_smul, hz, one_smul, add_comm]
    refine false_of_plus hVab hHV hHmax hM₁V hM₁0 hz hz' hzz' hcz hcz' hz'V hzz'V hz'N hzz'N
      hLA hyM hyH hyc (hM₁z' y hyM) (hM₁zz' y hyM) ?_
    rw [hzy]
    exact hsum y hyM hyH hp

theorem exists_fix_hyperplane {V H : Subgroup G}
    (hcop : Nat.Coprime (Nat.card V) (Nat.card M)) (hModd : Odd (Nat.card M))
    (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hVodd : Odd (Nat.card V)) (hHV : H ≤ V)
    (hHmax : ∀ K : Subgroup G, H ≤ K → K ≤ V → K = H ∨ K = V) (hHV' : H ≠ V)
    {M₁ : AddSubgroup M} (hM₁V : ∀ v ∈ V, ∀ m ∈ M₁, v • m ∈ M₁)
    (hM₁0 : ∀ m ∈ M₁, (∀ v ∈ V, v • m = m) → m = 0) {c z₁ z₂ : G}
    (hM₁c : ∀ m ∈ M₁, c • m ∈ M₁) (hM₁z₁ : ∀ m ∈ M₁, z₁ • m ∈ M₁)
    (hM₁z₂ : ∀ m ∈ M₁, z₂ • m ∈ M₁) (hc : c * c = 1) (h1 : z₁ * z₁ = 1) (h2 : z₂ * z₂ = 1)
    (hcz₁ : c * z₁ = z₁ * c) (hcz₂ : c * z₂ = z₂ * c) (h12 : z₁ * z₂ = z₂ * z₁)
    (hcV : ∀ v ∈ V, c * v * c⁻¹ = v⁻¹) (hz₁V : ∀ v ∈ V, z₁ * v * z₁⁻¹ ∈ V)
    (hz₂V : ∀ v ∈ V, z₂ * v * z₂⁻¹ ∈ V)
    (hLA : ∀ y : M, ∀ u ∈ ({z₁, z₂, z₁ * z₂} : Set G), c • y = y → u • y = -y → y = 0)
    {x : M} (hx : x ∈ M₁) (hxH : ∀ h ∈ H, h • x = x) (hx0 : x ≠ 0) :
    ∃ u ∈ ({z₁, z₂, z₁ * z₂} : Set G), (∀ h ∈ H, u * h * u⁻¹ ∈ H) ∧
      ∀ v ∈ V, u * v * u⁻¹ * v⁻¹ ∈ H := by
  classical
  haveI := Fintype.ofFinite H
  have hcopH : Nat.Coprime (2 * Nat.card H) (Nat.card M) :=
    Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_two_left.mpr hModd,
      Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hHV) hcop⟩
  have h3 : (z₁ * z₂) * (z₁ * z₂) = 1 := by
    calc (z₁ * z₂) * (z₁ * z₂) = z₁ * (z₂ * z₁) * z₂ := by group
      _ = z₁ * (z₁ * z₂) * z₂ := by rw [h12]
      _ = (z₁ * z₁) * (z₂ * z₂) := by group
      _ = 1 := by rw [h1, h2, one_mul]
  have hcz₃ : c * (z₁ * z₂) = (z₁ * z₂) * c := by
    rw [← mul_assoc, hcz₁, mul_assoc, hcz₂, mul_assoc]
  have hz₃V : ∀ v ∈ V, (z₁ * z₂) * v * (z₁ * z₂)⁻¹ ∈ V := fun v hv => by
    rw [show (z₁ * z₂) * v * (z₁ * z₂)⁻¹ = z₁ * (z₂ * v * z₂⁻¹) * z₁⁻¹ by group]
    exact hz₁V _ (hz₂V v hv)
  have hM₁z₃ : ∀ m ∈ M₁, (z₁ * z₂) • m ∈ M₁ := fun m hm => by
    rw [← smul_smul]; exact hM₁z₁ _ (hM₁z₂ m hm)
  have hm1 : z₁ ∈ ({z₁, z₂, z₁ * z₂} : Set G) := by simp
  have hm2 : z₂ ∈ ({z₁, z₂, z₁ * z₂} : Set G) := by simp
  have hm3 : z₁ * z₂ ∈ ({z₁, z₂, z₁ * z₂} : Set G) := by simp
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hcH : ∀ h ∈ H, c * h * c⁻¹ ∈ H := fun h hh => by
    rw [hcV h (hHV hh)]; exact H.inv_mem hh
  obtain ⟨x₁, hx₁M, hx₁H, hx₁c, hx₁0⟩ :
      ∃ x₁ ∈ M₁, (∀ h ∈ H, h • x₁ = x₁) ∧ c • x₁ = x₁ ∧ x₁ ≠ 0 := by
    by_cases hxc : x + c • x = 0
    · have hcx : c • x = -x := eq_neg_of_add_eq_zero_right hxc
      obtain ⟨v, hvV, hvH⟩ : ∃ v ∈ V, v ∉ H := by
        by_contra hcon
        push Not at hcon
        exact hHV' (le_antisymm hHV hcon)
      have hfix : ∀ w ∈ V, ∀ h ∈ H, h • (w • x) = w • x := fun w hw h hh => by
        rw [smul_smul, hVab h (hHV hh) w hw, ← smul_smul, hxH h hh]
      have hcw : ∀ w ∈ V, c • (w • x) = -(w⁻¹ • x) := fun w hw => by
        rw [smul_smul, show c * w = (c * w * c⁻¹) * c by group, hcV w hw, ← smul_smul, hcx,
          smul_neg]
      refine ⟨v • x - v⁻¹ • x, M₁.sub_mem (hM₁V v hvV x hx) (hM₁V _ (V.inv_mem hvV) x hx),
        fun h hh => by rw [smul_sub, hfix v hvV h hh, hfix _ (V.inv_mem hvV) h hh], ?_, ?_⟩
      · rw [smul_sub, hcw v hvV, hcw _ (V.inv_mem hvV), inv_inv]; abel
      · intro h0
        have hvv : v • x = v⁻¹ • x := sub_eq_zero.mp h0
        have hsq : (v ^ 2) • x = x := by
          rw [sq, ← smul_smul, hvv, smul_smul, mul_inv_cancel, one_smul]
        have hpow : ∀ k : ℕ, (v ^ 2) ^ k • x = x := by
          intro k
          induction k with
          | zero => simp
          | succ k ih => rw [pow_succ, ← smul_smul, hsq, ih]
        obtain ⟨k, hk⟩ := exists_pow_sq hVodd hvV
        have hvx : v • x = x := by rw [← hk]; exact hpow k
        let K : Subgroup G := MulAction.stabilizer G x ⊓ V
        have hHK : H ≤ K := fun h hh => ⟨(MulAction.mem_stabilizer_iff).mpr (hxH h hh), hHV hh⟩
        rcases hHmax K hHK inf_le_right with hK | hK
        · exact hvH (hK ▸ (⟨(MulAction.mem_stabilizer_iff).mpr hvx, hvV⟩ : v ∈ K))
        · exact hx0 (hM₁0 x hx fun w hw =>
            (MulAction.mem_stabilizer_iff).mp (hK ▸ hw : w ∈ K).1)
    · refine ⟨x + c • x, M₁.add_mem hx (hM₁c x hx), fun h hh => ?_, ?_, hxc⟩
      · rw [smul_add, hxH h hh, smul_smul,
          show h * c = c * (c * h * c⁻¹) by rw [hci, ← mul_assoc, ← mul_assoc, hc, one_mul], ← smul_smul, hxH _ (hcH h hh)]
      · rw [smul_add, smul_smul, hc, one_smul, add_comm]
  by_contra hcon
  push Not at hcon
  have hminus : ∀ u ∈ ({z₁, z₂, z₁ * z₂} : Set G), u * u = 1 →
      (∀ v ∈ V, u * v * u⁻¹ ∈ V) → (∀ h ∈ H, u * h * u⁻¹ ∈ H) →
      ∀ v ∈ V, u * v * u⁻¹ * v ∈ H := by
    intro u hu huu huV huN
    rcases plus_or_minus hVab hVodd hHV hHmax hHV' huu huV huN with hp | hm
    · obtain ⟨v, hv, hvH⟩ := hcon u hu huN
      exact absurd (hp v hv) hvH
    · exact hm
  have hLA1 := fun y => hLA y z₁ hm1
  have hLA2 := fun y => hLA y z₂ hm2
  by_cases n1 : ∀ h ∈ H, z₁ * h * z₁⁻¹ ∈ H
  · have m1 := hminus z₁ hm1 h1 hz₁V n1
    by_cases n2 : ∀ h ∈ H, z₂ * h * z₂⁻¹ ∈ H
    · obtain ⟨hN, hP⟩ := minus_mul_minus hVab hHV hz₁V hz₂V n1 n2 m1 (hminus z₂ hm2 h2 hz₂V n2)
      obtain ⟨v, hv, hvH⟩ := hcon _ hm3 hN
      exact hvH (hP v hv)
    by_cases n3 : ∀ h ∈ H, (z₁ * z₂) * h * (z₁ * z₂)⁻¹ ∈ H
    · obtain ⟨hN, -⟩ := minus_mul_minus hVab hHV hz₁V hz₃V n1 n3 m1 (hminus _ hm3 h3 hz₃V n3)
      have e : z₁ * (z₁ * z₂) = z₂ := by rw [← mul_assoc, h1, one_mul]
      rw [e] at hN
      exact n2 hN
    exact false_of_normalizing hcopH hVab hHV hHmax hM₁V hM₁0 h1 h2 h12 hcz₁ hcz₂ hz₂V hz₃V n1
      n2 n3 hLA2 hM₁z₁ hM₁z₂ hx₁M hx₁H hx₁c hx₁0
  by_cases n2 : ∀ h ∈ H, z₂ * h * z₂⁻¹ ∈ H
  · have m2 := hminus z₂ hm2 h2 hz₂V n2
    by_cases n3 : ∀ h ∈ H, (z₁ * z₂) * h * (z₁ * z₂)⁻¹ ∈ H
    · obtain ⟨hN, -⟩ := minus_mul_minus hVab hHV hz₃V hz₂V n3 n2 (hminus _ hm3 h3 hz₃V n3) m2
      have e : (z₁ * z₂) * z₂ = z₁ := by rw [mul_assoc, h2, mul_one]
      rw [e] at hN
      exact n1 hN
    have hz₂₁V : ∀ v ∈ V, (z₂ * z₁) * v * (z₂ * z₁)⁻¹ ∈ V := fun v hv => by
      rw [← h12]; exact hz₃V v hv
    have n3' : ¬ ∀ h ∈ H, (z₂ * z₁) * h * (z₂ * z₁)⁻¹ ∈ H := by rw [← h12]; exact n3
    exact false_of_normalizing hcopH hVab hHV hHmax hM₁V hM₁0 h2 h1 h12.symm hcz₂ hcz₁ hz₁V
      hz₂₁V n2 n1 n3' hLA1 hM₁z₂ hM₁z₁ hx₁M hx₁H hx₁c hx₁0
  by_cases n3 : ∀ h ∈ H, (z₁ * z₂) * h * (z₁ * z₂)⁻¹ ∈ H
  · have e : (z₁ * z₂) * z₁ = z₂ := by rw [mul_assoc, ← h12, ← mul_assoc, h1, one_mul]
    have e' : (z₁ * z₂) * z₁ = z₁ * (z₁ * z₂) := by rw [e, ← mul_assoc, h1, one_mul]
    have hV' : ∀ v ∈ V, ((z₁ * z₂) * z₁) * v * ((z₁ * z₂) * z₁)⁻¹ ∈ V := fun v hv => by
      rw [e]; exact hz₂V v hv
    have n2' : ¬ ∀ h ∈ H, ((z₁ * z₂) * z₁) * h * ((z₁ * z₂) * z₁)⁻¹ ∈ H := by rw [e]; exact n2
    exact false_of_normalizing hcopH hVab hHV hHmax hM₁V hM₁0 h3 h1 e' hcz₃ hcz₁ hz₁V
      hV' n3 n1 n2' hLA1 hM₁z₃ hM₁z₁ hx₁M hx₁H hx₁c hx₁0
  have hz₁xC : ∀ h ∈ H, (z₁ * h * z₁⁻¹) • (z₁ • x₁) = z₁ • x₁ := fun h hh => by
    rw [smul_smul, show z₁ * h * z₁⁻¹ * z₁ = z₁ * h by group, ← smul_smul, hx₁H h hh]
  have h0 := sum_smul_eq_zero hVab hHV hHmax hM₁V hM₁0 hz₁V n1 (hM₁z₁ x₁ hx₁M) hz₁xC
  refine false_of_plus hVab hHV hHmax hM₁V hM₁0 h1 h2 h12 hcz₁ hcz₂ hz₂V hz₃V n2 n3 hLA2 hx₁M
    hx₁H hx₁c (hM₁z₂ x₁ hx₁M) (hM₁z₃ x₁ hx₁M) ?_
  simp_rw [smul_add]
  rw [Finset.sum_add_distrib, h0, add_zero, sum_smul_const H hx₁H]
  exact nsmul_ne_zero_of_coprime
    (Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hHV) hcop) hx₁0

end

end CFSG.LocalAnalysis.WeakClosure81.OddCentral

