module

public import CFSG.LocalAnalysis.StandardType.GGKacK0V2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ggK1Sa_conj_injective {R : Type} [Group R]
    (hZ : ∀ z : R, (∀ g : R, g * z = z * g) → z = 1) :
    Function.Injective (MulAut.conj : R →* MulAut R) := by
  intro s t hst
  have h1 : MulAut.conj (t⁻¹ * s) = 1 := by
    rw [map_mul, map_inv, hst, inv_mul_cancel]
  have h2 : ∀ g : R, (t⁻¹ * s) * g = g * (t⁻¹ * s) := by
    intro g
    have h3 : (t⁻¹ * s) * g * (t⁻¹ * s)⁻¹ = g := by
      have h := congrFun (congrArg (fun e : MulAut R => (e : R → R)) h1) g
      rw [MulAut.conj_apply] at h
      simpa using h
    calc (t⁻¹ * s) * g = ((t⁻¹ * s) * g * (t⁻¹ * s)⁻¹) * (t⁻¹ * s) := by group
      _ = g * (t⁻¹ * s) := by rw [h3]
  exact (inv_mul_eq_one.mp (hZ _ (fun g => (h2 g).symm))).symm

private lemma ggK1Sa_comap_le_centralizer {R : Type} [Group R]
    (hZ : ∀ z : R, (∀ g : R, g * z = z * g) → z = 1)
    {p : ℕ} {A : Subgroup (MulAut R)} {x : R} (hxA : MulAut.conj x ∈ A)
    (hA : IsElemAbelian p A) :
    A.comap (MulAut.conj : R →* MulAut R) ≤ Subgroup.centralizer ({x} : Set R) := by
  intro s hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply ggK1Sa_conj_injective hZ
  rw [map_mul, map_mul]
  have hcomm := congrArg Subtype.val
    (hA.1.is_comm.comm ⟨MulAut.conj s, hs⟩ ⟨MulAut.conj x, hxA⟩)
  simpa using hcomm

private lemma ggK1Sa_isElemAbelian_comap {R : Type} [Group R]
    (hZ : ∀ z : R, (∀ g : R, g * z = z * g) → z = 1)
    {p : ℕ} {A : Subgroup (MulAut R)} (hA : IsElemAbelian p A) :
    IsElemAbelian p (A.comap (MulAut.conj : R →* MulAut R)) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · apply Subtype.ext
    show (a : R) * (b : R) = (b : R) * (a : R)
    apply ggK1Sa_conj_injective hZ
    rw [map_mul, map_mul]
    have hcomm := congrArg Subtype.val
      (hA.1.is_comm.comm ⟨MulAut.conj (a : R), a.2⟩ ⟨MulAut.conj (b : R), b.2⟩)
    simpa using hcomm
  · apply ggK1Sa_conj_injective hZ
    rw [map_pow, map_one]
    exact hA.2 (MulAut.conj a) ha

private lemma ggK1Sa_exists_comap_of_mem {R : Type} [Group R]
    {I : Set (MulAut R)} (hI : ∀ φ ∈ I, ∃ s : R, φ = MulAut.conj s)
    {A : Subgroup (MulAut R)}
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : R, φ l = a l) :
    ∀ a ∈ A, ∃ s : R, s ∈ A.comap (MulAut.conj : R →* MulAut R) ∧ a = MulAut.conj s := by
  intro a ha
  obtain ⟨φ, hφI, hφa⟩ := hAI a ha
  obtain ⟨s, hs⟩ := hI φ hφI
  have haeq : a = MulAut.conj s := by
    ext l
    rw [← hφa l, hs]
  exact ⟨s, by rw [Subgroup.mem_comap, ← haeq]; exact ha, haeq⟩

private lemma ggK1Sa_decomp_exists {R : Type} [Group R] {S C : Subgroup R}
    (hSC : ∀ a ∈ S, ∀ b ∈ C, a * b = b * a) :
    ∀ c ∈ S ⊔ C, ∃ uv : R × R, uv.1 ∈ S ∧ uv.2 ∈ C ∧ c = uv.1 * uv.2 := by
  let T : Subgroup R :=
    { carrier := {c | ∃ uv : R × R, uv.1 ∈ S ∧ uv.2 ∈ C ∧ c = uv.1 * uv.2}
      one_mem' := ⟨(1, 1), S.one_mem, C.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨⟨u₁, v₁⟩, hu₁, hv₁, rfl⟩ ⟨⟨u₂, v₂⟩, hu₂, hv₂, rfl⟩
        refine ⟨(u₁ * u₂, v₁ * v₂), S.mul_mem hu₁ hu₂, C.mul_mem hv₁ hv₂, ?_⟩
        calc (u₁ * v₁) * (u₂ * v₂) = u₁ * (v₁ * (u₂ * v₂)) := by rw [mul_assoc]
          _ = u₁ * ((v₁ * u₂) * v₂) := by rw [mul_assoc]
          _ = u₁ * ((u₂ * v₁) * v₂) := by rw [hSC u₂ hu₂ v₁ hv₁]
          _ = u₁ * (u₂ * (v₁ * v₂)) := by rw [mul_assoc]
          _ = (u₁ * u₂) * (v₁ * v₂) := by rw [mul_assoc]
      inv_mem' := by
        rintro a ⟨⟨u, v⟩, hu, hv, rfl⟩
        refine ⟨(u⁻¹, v⁻¹), S.inv_mem hu, C.inv_mem hv, ?_⟩
        rw [mul_inv_rev]
        exact (hSC u⁻¹ (S.inv_mem hu) v⁻¹ (C.inv_mem hv)).symm }
  intro c hc
  have hle : S ⊔ C ≤ T := sup_le
    (fun u hu => ⟨(u, 1), hu, C.one_mem, by simp⟩)
    (fun v hv => ⟨(1, v), S.one_mem, hv, by simp⟩)
  exact hle hc

private lemma ggK1Sa_decomp_unique {R : Type} [Group R] {S C : Subgroup R}
    (hdisj : Disjoint S C) {u₁ u₂ v₁ v₂ : R}
    (hu₁ : u₁ ∈ S) (hv₁ : v₁ ∈ C) (hu₂ : u₂ ∈ S) (hv₂ : v₂ ∈ C)
    (h : u₁ * v₁ = u₂ * v₂) : u₁ = u₂ ∧ v₁ = v₂ := by
  have hEq : u₂⁻¹ * u₁ = v₂ * v₁⁻¹ := by
    calc u₂⁻¹ * u₁ = (u₂⁻¹ * (u₁ * v₁)) * v₁⁻¹ := by group
      _ = (u₂⁻¹ * (u₂ * v₂)) * v₁⁻¹ := by rw [h]
      _ = v₂ * v₁⁻¹ := by group
  have hmem : u₂⁻¹ * u₁ ∈ S ⊓ C :=
    ⟨S.mul_mem (S.inv_mem hu₂) hu₁, hEq ▸ C.mul_mem hv₂ (C.inv_mem hv₁)⟩
  have hbot : u₂⁻¹ * u₁ = 1 := Subgroup.mem_bot.mp (hdisj.le_bot hmem)
  have hu : u₁ = u₂ := by
    have := congrArg (fun z => u₂ * z) hbot
    simpa using this
  have hv : v₂ = v₁ := by
    have hbot' : v₂ * v₁⁻¹ = 1 := hEq ▸ hbot
    have := congrArg (fun z => z * v₁) hbot'
    simpa [mul_assoc] using this
  exact ⟨hu, hv.symm⟩

private noncomputable def ggK1Sa_pair {R : Type} [Group R] {S C : Subgroup R}
    (hSC : ∀ a ∈ S, ∀ b ∈ C, a * b = b * a) (c : R) (hc : c ∈ S ⊔ C) : R × R :=
  Classical.choose (ggK1Sa_decomp_exists hSC c hc)

private lemma ggK1Sa_pair_fst_mem {R : Type} [Group R] {S C : Subgroup R}
    (hSC : ∀ a ∈ S, ∀ b ∈ C, a * b = b * a) {c : R} (hc : c ∈ S ⊔ C) :
    (ggK1Sa_pair hSC c hc).1 ∈ S :=
  (Classical.choose_spec (ggK1Sa_decomp_exists hSC c hc)).1

private lemma ggK1Sa_pair_snd_mem {R : Type} [Group R] {S C : Subgroup R}
    (hSC : ∀ a ∈ S, ∀ b ∈ C, a * b = b * a) {c : R} (hc : c ∈ S ⊔ C) :
    (ggK1Sa_pair hSC c hc).2 ∈ C :=
  (Classical.choose_spec (ggK1Sa_decomp_exists hSC c hc)).2.1

private lemma ggK1Sa_pair_mul {R : Type} [Group R] {S C : Subgroup R}
    (hSC : ∀ a ∈ S, ∀ b ∈ C, a * b = b * a) {c : R} (hc : c ∈ S ⊔ C) :
    (ggK1Sa_pair hSC c hc).1 * (ggK1Sa_pair hSC c hc).2 = c :=
  (Classical.choose_spec (ggK1Sa_decomp_exists hSC c hc)).2.2.symm

private noncomputable def ggK1Sa_u {R : Type} [Group R] {S C : Subgroup R}
    (hSC : ∀ a ∈ S, ∀ b ∈ C, a * b = b * a) (c : R) : R := by
  classical
  exact if h : c ∈ S ⊔ C then (ggK1Sa_pair hSC c h).1 else 1

private noncomputable def ggK1Sa_v {R : Type} [Group R] {S C : Subgroup R}
    (hSC : ∀ a ∈ S, ∀ b ∈ C, a * b = b * a) (c : R) : R := by
  classical
  exact if h : c ∈ S ⊔ C then (ggK1Sa_pair hSC c h).2 else 1

private lemma ggK1Sa_u_of_mem {R : Type} [Group R] {S C : Subgroup R}
    (hSC : ∀ a ∈ S, ∀ b ∈ C, a * b = b * a) {c : R} (hc : c ∈ S ⊔ C) :
    ggK1Sa_u hSC c = (ggK1Sa_pair hSC c hc).1 := by
  rw [ggK1Sa_u, dif_pos hc]

private lemma ggK1Sa_v_of_mem {R : Type} [Group R] {S C : Subgroup R}
    (hSC : ∀ a ∈ S, ∀ b ∈ C, a * b = b * a) {c : R} (hc : c ∈ S ⊔ C) :
    ggK1Sa_v hSC c = (ggK1Sa_pair hSC c hc).2 := by
  rw [ggK1Sa_v, dif_pos hc]

private lemma ggK1Sa_u_mem {R : Type} [Group R] {S C : Subgroup R}
    (hSC : ∀ a ∈ S, ∀ b ∈ C, a * b = b * a) {c : R} (hc : c ∈ S ⊔ C) :
    ggK1Sa_u hSC c ∈ S := by
  rw [ggK1Sa_u_of_mem hSC hc]
  exact ggK1Sa_pair_fst_mem hSC hc

private lemma ggK1Sa_v_mem {R : Type} [Group R] {S C : Subgroup R}
    (hSC : ∀ a ∈ S, ∀ b ∈ C, a * b = b * a) {c : R} (hc : c ∈ S ⊔ C) :
    ggK1Sa_v hSC c ∈ C := by
  rw [ggK1Sa_v_of_mem hSC hc]
  exact ggK1Sa_pair_snd_mem hSC hc

private lemma ggK1Sa_u_mul_v {R : Type} [Group R] {S C : Subgroup R}
    (hSC : ∀ a ∈ S, ∀ b ∈ C, a * b = b * a) {c : R} (hc : c ∈ S ⊔ C) :
    ggK1Sa_u hSC c * ggK1Sa_v hSC c = c := by
  rw [ggK1Sa_u_of_mem hSC hc, ggK1Sa_v_of_mem hSC hc]
  exact ggK1Sa_pair_mul hSC hc

private lemma ggK1Sa_u_self {R : Type} [Group R] {S C : Subgroup R}
    (hSC : ∀ a ∈ S, ∀ b ∈ C, a * b = b * a) (hdisj : Disjoint S C)
    {c : R} (hc : c ∈ S) : ggK1Sa_u hSC c = c := by
  have hc' : c ∈ S ⊔ C := Subgroup.mem_sup_left hc
  have h1 : ggK1Sa_u hSC c * ggK1Sa_v hSC c = c := ggK1Sa_u_mul_v hSC hc'
  have huniq := ggK1Sa_decomp_unique hdisj (ggK1Sa_u_mem hSC hc') (ggK1Sa_v_mem hSC hc')
    hc C.one_mem (h1.trans (mul_one c).symm)
  exact huniq.1

private lemma ggK1Sa_u_mul {R : Type} [Group R] {S C : Subgroup R}
    (hSC : ∀ a ∈ S, ∀ b ∈ C, a * b = b * a) (hdisj : Disjoint S C)
    {c d : R} (hc : c ∈ S ⊔ C) (hd : d ∈ S ⊔ C) :
    ggK1Sa_u hSC (c * d) = ggK1Sa_u hSC c * ggK1Sa_u hSC d := by
  have hcd : c * d ∈ S ⊔ C := Subgroup.mul_mem _ hc hd
  have h1 : ggK1Sa_u hSC (c * d) * ggK1Sa_v hSC (c * d) = c * d :=
    ggK1Sa_u_mul_v hSC hcd
  have hstep : (ggK1Sa_u hSC c * ggK1Sa_u hSC d) * (ggK1Sa_v hSC c * ggK1Sa_v hSC d)
      = (ggK1Sa_u hSC c * ggK1Sa_v hSC c) * (ggK1Sa_u hSC d * ggK1Sa_v hSC d) := by
    calc (ggK1Sa_u hSC c * ggK1Sa_u hSC d) * (ggK1Sa_v hSC c * ggK1Sa_v hSC d)
        = ggK1Sa_u hSC c
            * (ggK1Sa_u hSC d * (ggK1Sa_v hSC c * ggK1Sa_v hSC d)) := by rw [mul_assoc]
      _ = ggK1Sa_u hSC c
            * ((ggK1Sa_u hSC d * ggK1Sa_v hSC c) * ggK1Sa_v hSC d) := by rw [mul_assoc]
      _ = ggK1Sa_u hSC c
            * ((ggK1Sa_v hSC c * ggK1Sa_u hSC d) * ggK1Sa_v hSC d) := by
            rw [hSC (ggK1Sa_u hSC d) (ggK1Sa_u_mem hSC hd)
              (ggK1Sa_v hSC c) (ggK1Sa_v_mem hSC hc)]
      _ = ggK1Sa_u hSC c
            * (ggK1Sa_v hSC c * (ggK1Sa_u hSC d * ggK1Sa_v hSC d)) := by rw [mul_assoc]
      _ = (ggK1Sa_u hSC c * ggK1Sa_v hSC c)
            * (ggK1Sa_u hSC d * ggK1Sa_v hSC d) := by rw [mul_assoc]
  have h2 : (ggK1Sa_u hSC c * ggK1Sa_u hSC d) * (ggK1Sa_v hSC c * ggK1Sa_v hSC d)
      = c * d := by
    rw [hstep, ggK1Sa_u_mul_v hSC hc, ggK1Sa_u_mul_v hSC hd]
  have huniq := ggK1Sa_decomp_unique hdisj (ggK1Sa_u_mem hSC hcd) (ggK1Sa_v_mem hSC hcd)
    (S.mul_mem (ggK1Sa_u_mem hSC hc) (ggK1Sa_u_mem hSC hd))
    (C.mul_mem (ggK1Sa_v_mem hSC hc) (ggK1Sa_v_mem hSC hd))
    (h1.trans h2.symm)
  exact huniq.1

private lemma ggK1Sa_u_x_central {R : Type} [Group R] {S C : Subgroup R}
    (hSC : ∀ a ∈ S, ∀ b ∈ C, a * b = b * a) {x : R}
    (hsup : S ⊔ C = Subgroup.centralizer ({x} : Set R)) (hx : x ∈ S ⊔ C) :
    ∀ y ∈ S, ggK1Sa_u hSC x * y = y * ggK1Sa_u hSC x := by
  intro y hy
  have hycent : y ∈ Subgroup.centralizer ({x} : Set R) := by
    rw [← hsup]; exact Subgroup.mem_sup_left hy
  have hyx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp hycent
  have hux : ggK1Sa_u hSC x * ggK1Sa_v hSC x = x := ggK1Sa_u_mul_v hSC hx
  have hvC : ggK1Sa_v hSC x ∈ C := ggK1Sa_v_mem hSC hx
  calc ggK1Sa_u hSC x * y
      = (ggK1Sa_u hSC x * y) * (ggK1Sa_v hSC x * (ggK1Sa_v hSC x)⁻¹) := by group
    _ = (ggK1Sa_u hSC x * (y * ggK1Sa_v hSC x)) * (ggK1Sa_v hSC x)⁻¹ := by group
    _ = (ggK1Sa_u hSC x * (ggK1Sa_v hSC x * y)) * (ggK1Sa_v hSC x)⁻¹ := by
          rw [hSC y hy (ggK1Sa_v hSC x) hvC]
    _ = ((ggK1Sa_u hSC x * ggK1Sa_v hSC x) * y) * (ggK1Sa_v hSC x)⁻¹ := by group
    _ = (x * y) * (ggK1Sa_v hSC x)⁻¹ := by rw [hux]
    _ = (y * x) * (ggK1Sa_v hSC x)⁻¹ := by rw [hyx]
    _ = (y * (ggK1Sa_u hSC x * ggK1Sa_v hSC x)) * (ggK1Sa_v hSC x)⁻¹ := by rw [hux]
    _ = y * ggK1Sa_u hSC x := by group

private lemma ggK1Sa_u_inv {R : Type} [Group R] {S C : Subgroup R}
    (hSC : ∀ a ∈ S, ∀ b ∈ C, a * b = b * a) (hdisj : Disjoint S C)
    {c : R} (hc : c ∈ S ⊔ C) :
    ggK1Sa_u hSC c⁻¹ = (ggK1Sa_u hSC c)⁻¹ := by
  have hc' : c⁻¹ ∈ S ⊔ C := Subgroup.inv_mem _ hc
  have hcomm : Commute (ggK1Sa_u hSC c) (ggK1Sa_v hSC c) :=
    hSC _ (ggK1Sa_u_mem hSC hc) _ (ggK1Sa_v_mem hSC hc)
  have h2 : (ggK1Sa_u hSC c)⁻¹ * (ggK1Sa_v hSC c)⁻¹ = c⁻¹ := by
    rw [(hcomm.inv_inv).eq, ← mul_inv_rev, ggK1Sa_u_mul_v hSC hc]
  exact (ggK1Sa_decomp_unique hdisj (ggK1Sa_u_mem hSC hc') (ggK1Sa_v_mem hSC hc')
    (S.inv_mem (ggK1Sa_u_mem hSC hc)) (C.inv_mem (ggK1Sa_v_mem hSC hc))
    ((ggK1Sa_u_mul_v hSC hc').trans h2.symm)).1

private lemma ggK1Sa_u_zpow {R : Type} [Group R] {S C : Subgroup R}
    (hSC : ∀ a ∈ S, ∀ b ∈ C, a * b = b * a) (hdisj : Disjoint S C)
    {c : R} (hc : c ∈ S ⊔ C) (k : ℤ) :
    ggK1Sa_u hSC (c ^ k) = (ggK1Sa_u hSC c) ^ k := by
  have hnat : ∀ n : ℕ, ggK1Sa_u hSC (c ^ n) = (ggK1Sa_u hSC c) ^ n := by
    intro n
    induction n with
    | zero => simp [ggK1Sa_u_self hSC hdisj S.one_mem]
    | succ n ih =>
        rw [pow_succ, ggK1Sa_u_mul hSC hdisj (Subgroup.pow_mem _ hc n) hc, ih, pow_succ]
  have hneg : ∀ n : ℕ, ggK1Sa_u hSC (c ^ (-(n : ℤ))) = (ggK1Sa_u hSC c) ^ (-(n : ℤ)) := by
    intro n
    rw [zpow_neg, zpow_natCast, ggK1Sa_u_inv hSC hdisj (Subgroup.pow_mem _ hc n), hnat n,
      zpow_neg, zpow_natCast]
  rcases Int.eq_nat_or_neg k with ⟨n, hk | hk⟩
  · rw [hk]; simpa only [zpow_natCast] using hnat n
  · rw [hk]; exact hneg n

private lemma ggK1Sa_isElemAbelian_subgroupOf {p : ℕ} {G : Type} [Group G]
    {H K : Subgroup G} (hH : IsElemAbelian p H) :
    IsElemAbelian p (H.subgroupOf K) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val
      (hH.1.is_comm.comm ⟨(a : G), Subgroup.mem_subgroupOf.mp a.2⟩
        ⟨(b : G), Subgroup.mem_subgroupOf.mp b.2⟩)
  · apply Subtype.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using
      (hH.2 (a : G) (Subgroup.mem_subgroupOf.mp ha))

private lemma ggK1Sa_isElemAbelian_map {p : ℕ} {G N : Type} [Group G] [Group N]
    (f : G →* N) {H : Subgroup G} (hH : IsElemAbelian p H) :
    IsElemAbelian p (H.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    show (a : N) * (b : N) = (b : N) * (a : N)
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    have hxy : x * y = y * x := congrArg Subtype.val (hH.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [hxy]
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp ha
    rw [← hxa, ← map_pow, hH.2 x hx, map_one]

theorem ggK1_sigma_abstract {p : ℕ} {R : Type} [Group R]
    (hZ : ∀ z : R, (∀ g : R, g * z = z * g) → z = 1)
    (I : Set (MulAut R)) (hI : ∀ φ ∈ I, ∃ s : R, φ = MulAut.conj s)
    (x : R) (S C : Subgroup R)
    (hSC : ∀ a ∈ S, ∀ b ∈ C, a * b = b * a) (hdisj : Disjoint S C)
    (hsup : S ⊔ C = Subgroup.centralizer ({x} : Set R))
    (hcomp : ∀ J : Subgroup R, CFSG.Assembly.IsComponentOf J (ggFixSub (MulAut.conj x)) →
      ∀ j ∈ J, ∀ a ∈ S, a * j = j * a)
    {t₀ a₀ : R} (ht₀ : t₀ ∈ S) (ha₀ : a₀ ∈ S) (ht₀p : t₀ ^ p = 1)
    (hnc : a₀ * t₀ ≠ t₀ * a₀)
    (A : Subgroup (MulAut R)) (hxA : (MulAut.conj x : MulAut R) ∈ A) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : R, φ l = a l) :
    ∃ t : R, t ^ p = 1 ∧ (∀ a ∈ A, a t = t) ∧
      (∀ J : Subgroup R, CFSG.Assembly.IsComponentOf J (ggFixSub (MulAut.conj x)) →
        ∀ j ∈ J, t * j = j * t) ∧
      (MulAut.conj t : MulAut R) ∉ Subgroup.zpowers (MulAut.conj x) := by
  let Ã : Subgroup R := A.comap (MulAut.conj : R →* MulAut R)
  have hÃcent : Ã ≤ Subgroup.centralizer ({x} : Set R) :=
    ggK1Sa_comap_le_centralizer hZ hxA hA
  have hÃelem : IsElemAbelian p Ã := ggK1Sa_isElemAbelian_comap hZ hA
  have hxÃ : x ∈ Ã := by rw [Subgroup.mem_comap]; exact hxA
  have hxsup : x ∈ S ⊔ C := by
    rw [hsup]; exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  by_cases hcase : ∃ s : ↥Ã, ggK1Sa_u hSC (s : R) ∉ Subgroup.zpowers (ggK1Sa_u hSC x)
  · obtain ⟨s, hs⟩ := hcase
    have hssup : (s : R) ∈ S ⊔ C := by rw [hsup]; exact hÃcent s.2
    have huS : ggK1Sa_u hSC (s : R) ∈ S := ggK1Sa_u_mem hSC hssup
    refine ⟨ggK1Sa_u hSC (s : R), ?_, ?_, ?_, ?_⟩
    · have hsp : (s : R) ^ p = 1 := hÃelem.2 (s : R) s.2
      have hvC : ggK1Sa_v hSC (s : R) ∈ C := ggK1Sa_v_mem hSC hssup
      have hcommuv : Commute (ggK1Sa_u hSC (s : R)) (ggK1Sa_v hSC (s : R)) :=
        hSC _ huS _ hvC
      have hprod : ggK1Sa_u hSC (s : R) ^ p * ggK1Sa_v hSC (s : R) ^ p = 1 := by
        rw [← hcommuv.mul_pow p, ggK1Sa_u_mul_v hSC hssup, hsp]
      have hupC : ggK1Sa_u hSC (s : R) ^ p ∈ C := by
        have heq : ggK1Sa_u hSC (s : R) ^ p = (ggK1Sa_v hSC (s : R) ^ p)⁻¹ := by
          calc ggK1Sa_u hSC (s : R) ^ p
              = (ggK1Sa_u hSC (s : R) ^ p * ggK1Sa_v hSC (s : R) ^ p)
                  * (ggK1Sa_v hSC (s : R) ^ p)⁻¹ := by group
            _ = 1 * (ggK1Sa_v hSC (s : R) ^ p)⁻¹ := by rw [hprod]
            _ = (ggK1Sa_v hSC (s : R) ^ p)⁻¹ := by rw [one_mul]
        rw [heq]
        exact C.inv_mem (C.pow_mem hvC p)
      have hup1 : ggK1Sa_u hSC (s : R) ^ p = 1 :=
        Subgroup.mem_bot.mp (hdisj.le_bot ⟨S.pow_mem huS p, hupC⟩)
      exact hup1
    · intro a ha
      obtain ⟨s', hs'Ã, haeq⟩ := ggK1Sa_exists_comap_of_mem hI hAI a ha
      have hs'sup : (s' : R) ∈ S ⊔ C := by rw [hsup]; exact hÃcent hs'Ã
      have hu'S : ggK1Sa_u hSC (s' : R) ∈ S := ggK1Sa_u_mem hSC hs'sup
      have hv'C : ggK1Sa_v hSC (s' : R) ∈ C := ggK1Sa_v_mem hSC hs'sup
      have hcomm_ss' : (s : R) * (s' : R) = (s' : R) * (s : R) := by
        have := congrArg Subtype.val (hÃelem.1.is_comm.comm s ⟨s', hs'Ã⟩)
        simpa using this
      have hmul1 : ggK1Sa_u hSC ((s : R) * (s' : R))
          = ggK1Sa_u hSC (s : R) * ggK1Sa_u hSC (s' : R) :=
        ggK1Sa_u_mul hSC hdisj hssup hs'sup
      have hmul2 : ggK1Sa_u hSC ((s' : R) * (s : R))
          = ggK1Sa_u hSC (s' : R) * ggK1Sa_u hSC (s : R) :=
        ggK1Sa_u_mul hSC hdisj hs'sup hssup
      have hcomm_uu : ggK1Sa_u hSC (s : R) * ggK1Sa_u hSC (s' : R)
          = ggK1Sa_u hSC (s' : R) * ggK1Sa_u hSC (s : R) := by
        rw [← hmul1, ← hmul2, hcomm_ss']
      have hconj : MulAut.conj s' (ggK1Sa_u hSC (s : R)) = ggK1Sa_u hSC (s : R) := by
        have h1 : ggK1Sa_v hSC (s' : R) * ggK1Sa_u hSC (s : R)
            * (ggK1Sa_v hSC (s' : R))⁻¹ = ggK1Sa_u hSC (s : R) := by
          rw [(hSC (ggK1Sa_u hSC (s : R)) huS
            (ggK1Sa_v hSC (s' : R)) hv'C).symm]
          group
        rw [MulAut.conj_apply]
        conv_lhs => rw [← ggK1Sa_u_mul_v hSC hs'sup]
        rw [show (ggK1Sa_u hSC (s' : R) * ggK1Sa_v hSC (s' : R))
              * ggK1Sa_u hSC (s : R)
              * (ggK1Sa_u hSC (s' : R) * ggK1Sa_v hSC (s' : R))⁻¹
            = ggK1Sa_u hSC (s' : R)
              * (ggK1Sa_v hSC (s' : R) * ggK1Sa_u hSC (s : R)
                  * (ggK1Sa_v hSC (s' : R))⁻¹)
              * (ggK1Sa_u hSC (s' : R))⁻¹ by group]
        rw [h1, ← hcomm_uu]
        group
      rw [haeq]
      exact hconj
    · intro J hJ j hj
      exact hcomp J hJ j hj (ggK1Sa_u hSC (s : R)) huS
    · intro hmem
      rw [Subgroup.mem_zpowers_iff] at hmem
      obtain ⟨k, hk⟩ := hmem
      have hk' : MulAut.conj (x ^ k) = MulAut.conj (ggK1Sa_u hSC (s : R)) := by
        rw [map_zpow]; exact hk
      have htx : x ^ k = ggK1Sa_u hSC (s : R) := ggK1Sa_conj_injective hZ hk'
      apply hs
      rw [Subgroup.mem_zpowers_iff]
      have hx'eq : ggK1Sa_u hSC (x ^ k) = (ggK1Sa_u hSC x) ^ k :=
        ggK1Sa_u_zpow hSC hdisj hxsup k
      have hx'S : x ^ k ∈ S := by rw [htx]; exact huS
      have hself : ggK1Sa_u hSC (x ^ k) = x ^ k := ggK1Sa_u_self hSC hdisj hx'S
      exact ⟨k, by rw [← hx'eq, hself, htx]⟩
  · push Not at hcase
    refine ⟨t₀, ht₀p, ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨s', hs'Ã, haeq⟩ := ggK1Sa_exists_comap_of_mem hI hAI a ha
      have hs'sup : (s' : R) ∈ S ⊔ C := by rw [hsup]; exact hÃcent hs'Ã
      have hv'C : ggK1Sa_v hSC (s' : R) ∈ C := ggK1Sa_v_mem hSC hs'sup
      have hu'pow : ggK1Sa_u hSC (s' : R) ∈ Subgroup.zpowers (ggK1Sa_u hSC x) :=
        hcase ⟨s', hs'Ã⟩
      rw [Subgroup.mem_zpowers_iff] at hu'pow
      obtain ⟨m, hm⟩ := hu'pow
      have huxa : Commute (ggK1Sa_u hSC x) t₀ := ggK1Sa_u_x_central hSC hsup hxsup t₀ ht₀
      have hu't₀ : Commute (ggK1Sa_u hSC (s' : R)) t₀ := by
        rw [← hm]; exact huxa.zpow_left m
      have hv't₀ : ggK1Sa_v hSC (s' : R) * t₀ = t₀ * ggK1Sa_v hSC (s' : R) :=
        (hSC t₀ ht₀ (ggK1Sa_v hSC (s' : R)) hv'C).symm
      have hconj : MulAut.conj s' t₀ = t₀ := by
        have h1 : ggK1Sa_v hSC (s' : R) * t₀ * (ggK1Sa_v hSC (s' : R))⁻¹ = t₀ := by
          rw [hv't₀]; group
        rw [MulAut.conj_apply]
        conv_lhs => rw [← ggK1Sa_u_mul_v hSC hs'sup]
        rw [show (ggK1Sa_u hSC (s' : R) * ggK1Sa_v hSC (s' : R)) * t₀
              * (ggK1Sa_u hSC (s' : R) * ggK1Sa_v hSC (s' : R))⁻¹
            = ggK1Sa_u hSC (s' : R)
              * (ggK1Sa_v hSC (s' : R) * t₀ * (ggK1Sa_v hSC (s' : R))⁻¹)
              * (ggK1Sa_u hSC (s' : R))⁻¹ by group]
        rw [h1, hu't₀.eq]
        group
      rw [haeq]
      exact hconj
    · intro J hJ j hj
      exact hcomp J hJ j hj t₀ ht₀
    · intro hmem
      rw [Subgroup.mem_zpowers_iff] at hmem
      obtain ⟨k, hk⟩ := hmem
      have hk' : MulAut.conj (x ^ k) = MulAut.conj t₀ := by rw [map_zpow]; exact hk
      have htx : x ^ k = t₀ := ggK1Sa_conj_injective hZ hk'
      have ha₀cent : a₀ ∈ Subgroup.centralizer ({x} : Set R) := by
        rw [← hsup]; exact Subgroup.mem_sup_left ha₀
      have hxa : Commute x a₀ := (Subgroup.mem_centralizer_singleton_iff.mp ha₀cent).symm
      have hcomm : t₀ * a₀ = a₀ * t₀ := by
        rw [← htx]
        exact (Commute.zpow_left hxa k).eq
      exact hnc hcomm.symm

theorem ggK1_sigma_abstract_hom {p : ℕ} {R : Type} [Group R]
    (hZ : ∀ z : R, (∀ g : R, g * z = z * g) → z = 1)
    (I : Set (MulAut R)) (hI : ∀ φ ∈ I, ∃ s : R, φ = MulAut.conj s)
    (x : R) (S : Subgroup ↥(Subgroup.centralizer ({x} : Set R))) (hSn : S.Normal)
    {F : Type} [Group F] (ρ : ↥(Subgroup.centralizer ({x} : Set R)) →* F)
    (hinj : Function.Injective (ρ.comp S.subtype))
    (hcomp : ∀ J : Subgroup R, CFSG.Assembly.IsComponentOf J (ggFixSub (MulAut.conj x)) →
      ∀ j ∈ J, ∀ a ∈ S, (a : R) * j = j * (a : R))
    (hP : ∀ P : Subgroup F, IsElemAbelian p P →
      ∃ t : ↥(Subgroup.centralizer ({x} : Set R)), t ∈ S ∧ t ^ p = 1 ∧
        (∀ u ∈ P, u * ρ t = ρ t * u) ∧
        ∃ a₀ : ↥(Subgroup.centralizer ({x} : Set R)), a₀ * t ≠ t * a₀)
    (A : Subgroup (MulAut R)) (hxA : (MulAut.conj x : MulAut R) ∈ A) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : R, φ l = a l) :
    ∃ t : R, t ^ p = 1 ∧ (∀ a ∈ A, a t = t) ∧
      (∀ J : Subgroup R, CFSG.Assembly.IsComponentOf J (ggFixSub (MulAut.conj x)) →
        ∀ j ∈ J, t * j = j * t) ∧
      (MulAut.conj t : MulAut R) ∉ Subgroup.zpowers (MulAut.conj x) := by
  let Ã : Subgroup R := A.comap (MulAut.conj : R →* MulAut R)
  have hÃcent : Ã ≤ Subgroup.centralizer ({x} : Set R) :=
    ggK1Sa_comap_le_centralizer hZ hxA hA
  have hÃelem : IsElemAbelian p Ã := ggK1Sa_isElemAbelian_comap hZ hA
  let Ã' : Subgroup ↥(Subgroup.centralizer ({x} : Set R)) :=
    Ã.subgroupOf (Subgroup.centralizer ({x} : Set R))
  have hÃ'elem : IsElemAbelian p Ã' := ggK1Sa_isElemAbelian_subgroupOf hÃelem
  have hP_elem : IsElemAbelian p (Ã'.map ρ) := ggK1Sa_isElemAbelian_map ρ hÃ'elem
  obtain ⟨t, htS, htp, hcommP, a₀, ha₀⟩ := hP (Ã'.map ρ) hP_elem
  refine ⟨(t : R), ?_, ?_, ?_, ?_⟩
  · have := congrArg Subtype.val htp
    simpa using this
  · intro a ha
    obtain ⟨s, hsÃ, haeq⟩ := ggK1Sa_exists_comap_of_mem hI hAI a ha
    have hscent : s ∈ Subgroup.centralizer ({x} : Set R) := hÃcent hsÃ
    let sG : ↥(Subgroup.centralizer ({x} : Set R)) := ⟨s, hscent⟩
    have hsG' : sG ∈ Ã' := by
      rw [Subgroup.mem_subgroupOf]
      exact hsÃ
    have hcomm := hcommP (ρ sG) (Subgroup.mem_map_of_mem ρ hsG')
    have hmemS : sG * t * sG⁻¹ ∈ S := hSn.conj_mem t htS sG
    have hρeq : (ρ.comp S.subtype) ⟨sG * t * sG⁻¹, hmemS⟩ = (ρ.comp S.subtype) ⟨t, htS⟩ := by
      simp only [MonoidHom.comp_apply, Subgroup.subtype_apply]
      rw [map_mul, map_mul, map_inv, hcomm]
      group
    have ht_eq : sG * t * sG⁻¹ = t := congrArg Subtype.val (hinj hρeq)
    have hGcomm : sG * t = t * sG := by
      have := congrArg (fun z => z * sG) ht_eq
      simpa [mul_assoc] using this
    have hRcomm : s * (t : R) = (t : R) * s := by
      simpa using congrArg Subtype.val hGcomm
    rw [haeq]
    show MulAut.conj s (t : R) = (t : R)
    rw [MulAut.conj_apply, hRcomm]
    group
  · intro J hJ j hj
    exact hcomp J hJ j hj t htS
  · intro hmem
    rw [Subgroup.mem_zpowers_iff] at hmem
    obtain ⟨k, hk⟩ := hmem
    have hk' : MulAut.conj (x ^ k) = MulAut.conj (t : R) := by rw [map_zpow]; exact hk
    have htx : x ^ k = (t : R) := ggK1Sa_conj_injective hZ hk'
    have htcentral : ∀ g : ↥(Subgroup.centralizer ({x} : Set R)), g * t = t * g := by
      intro g
      apply Subtype.ext
      show (g : R) * (t : R) = (t : R) * (g : R)
      rw [← htx]
      have hgx : Commute (g : R) x := Subgroup.mem_centralizer_singleton_iff.mp g.2
      exact (Commute.zpow_right hgx k).eq
    exact ha₀ (htcentral a₀)

end CFSG.StandardType

end
