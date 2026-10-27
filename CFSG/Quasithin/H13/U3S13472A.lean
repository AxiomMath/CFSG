module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.H13.U3.P2

open CFSG.Open CFSG.Quasithin

open MulAction in
theorem mem_closure_of_fixed_odd {K M : Type*} [Group K] [Finite K] [CommGroup M] [Finite M]
    (h2 : ∀ m : M, m ^ 2 = 1) (c : K →* MulAut M)
    (hC : ∀ m : M, (∀ k, c k m = m) → m = 1) {S : Subgroup K} (hS : ¬ 2 ∣ S.index)
    {v : M} (hv : ∀ s ∈ S, c s v = v) :
    v ∈ Subgroup.closure {w | ∃ k m, c k m * m⁻¹ = w} := by
  classical
  let _ : MulAction K M := MulAction.compHom M c
  set O : Finset M := (Set.toFinite (orbit K v)).toFinset with hO
  have hmemO : ∀ w, w ∈ O ↔ w ∈ orbit K v := fun w => Set.Finite.mem_toFinset _
  have hfix : ∀ k : K, c k (∏ w ∈ O, w) = ∏ w ∈ O, w := by
    intro k
    rw [map_prod]
    refine Finset.prod_nbij' (fun w => c k w) (fun w => c k⁻¹ w) ?_ ?_ ?_ ?_ ?_
    · intro w hw
      rw [hmemO] at hw ⊢
      obtain ⟨g, rfl⟩ := hw
      exact ⟨k * g, show (k * g) • v = c k (g • v) by rw [mul_smul]; rfl⟩
    · intro w hw
      rw [hmemO] at hw ⊢
      obtain ⟨g, rfl⟩ := hw
      exact ⟨k⁻¹ * g, show (k⁻¹ * g) • v = c k⁻¹ (g • v) by rw [mul_smul]; rfl⟩
    · intro w _
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    · intro w _
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    · intro w _
      rfl
  have hp : ∏ w ∈ O, w = 1 := hC _ hfix
  have hstab : S ≤ stabilizer K v := fun s hs => (hv s hs : c s v = v)
  have hodd : ¬ 2 ∣ O.card := by
    have h1 : O.card = (orbit K v).ncard := by
      rw [hO, Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    rw [h1, ← index_stabilizer]
    exact fun h => hS (h.trans (Subgroup.index_dvd_of_le hstab))
  have hv1 : v⁻¹ = v := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, h2]
  have key : ∏ w ∈ O, (w * v⁻¹) = v := by
    rw [Finset.prod_mul_distrib, hp, one_mul, Finset.prod_const, hv1]
    obtain ⟨n, hn⟩ := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)
    rw [hn, pow_add, pow_mul, h2, one_pow, one_mul, pow_one]
  rw [← key]
  refine Subgroup.prod_mem _ fun w hw => Subgroup.subset_closure ?_
  rw [hmemO] at hw
  obtain ⟨k, rfl⟩ := hw
  exact ⟨k, v, rfl⟩

section Comm

variable {V : Type*} [CommGroup V]

theorem apply_comm {f k : MulAut V} (h : f * k = k * f) (v : V) : f (k v) = k (f v) := by
  have := DFunLike.congr_fun h v
  simpa only [MulAut.mul_apply] using this

theorem apply_inv_apply (k : MulAut V) (v : V) : k (k⁻¹ v) = v := k.apply_symm_apply v

theorem inv_apply_apply (k : MulAut V) (v : V) : k⁻¹ (k v) = v := k.symm_apply_apply v

theorem apply_mem_commV_of_comm {F : Subgroup (MulAut V)} {k : MulAut V}
    (hk : ∀ f ∈ F, f * k = k * f) {u : V} (hu : u ∈ commV F) : k u ∈ commV F := by
  induction hu using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨f, hf, v, rfl⟩ := hw
    apply Subgroup.subset_closure
    refine ⟨f, hf, k v, ?_⟩
    rw [map_mul, map_inv, apply_comm (hk f hf)]
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

theorem mul_mul_mul_inv_cancel (a b c : V) : a * b * (c * a⁻¹) = c * b := by
  rw [mul_comm a b, mul_assoc, mul_comm a (c * a⁻¹), mul_assoc c, inv_mul_cancel, mul_one,
    mul_comm]

theorem fix_commV_of_triv {R K : Subgroup (MulAut V)}
    (hRK : ∀ r ∈ R, ∀ k ∈ K, r * k = k * r) (htriv : ∀ k ∈ K, ∀ u ∈ commV R, k u = u)
    {r : MulAut V} (hr : r ∈ R) {u : V} (hu : u ∈ commV K) : r u = u := by
  induction hu using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨k, hk, v, rfl⟩ := hw
    have hu : r v * v⁻¹ ∈ commV R := Subgroup.subset_closure ⟨r, hr, v, rfl⟩
    have h1 : k (r v * v⁻¹) = r v * v⁻¹ := htriv k hk _ hu
    rw [map_mul, map_inv] at h1
    rw [map_mul, map_inv, apply_comm (hRK r hr k hk)]
    calc k (r v) * (r v)⁻¹ = (k (r v) * (k v)⁻¹) * (k v * (r v)⁻¹) := by group
      _ = (r v * v⁻¹) * (k v * (r v)⁻¹) := by rw [h1]
      _ = k v * v⁻¹ := mul_mul_mul_inv_cancel _ _ _
  | one => exact map_one r
  | mul a b _ _ ha hb => rw [map_mul, ha, hb]
  | inv a _ ha => rw [map_inv, ha]

@[expose] def triv (K : Subgroup (MulAut V)) (U : Subgroup V) (hKU : ∀ k ∈ K, ∀ u ∈ U, k u ∈ U) :
    Subgroup ↥K where
  carrier := {k | ∀ u ∈ U, (k : MulAut V) u = u}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb u hu => by
    show (a : MulAut V) ((b : MulAut V) u) = u
    rw [hb u hu, ha u hu]
  inv_mem' := fun {a} ha u hu => by
    show (a : MulAut V)⁻¹ u = u
    have h1 : (a : MulAut V) ((a : MulAut V)⁻¹ u) = (a : MulAut V)⁻¹ u :=
      ha _ (hKU _ (inv_mem a.2) u hu)
    rw [apply_inv_apply] at h1
    exact h1.symm

theorem triv_normal (K : Subgroup (MulAut V)) (U : Subgroup V)
    (hKU : ∀ k ∈ K, ∀ u ∈ U, k u ∈ U) : (triv K U hKU).Normal := by
  refine ⟨fun k hk g u hu => ?_⟩
  have hk' : ∀ u ∈ U, (k : MulAut V) u = u := hk
  show ((g * k * g⁻¹ : ↥K) : MulAut V) u = u
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply]
  rw [hk' _ (hKU _ (inv_mem g.2) u hu), apply_inv_apply]

theorem triv_of_mem {K : Subgroup (MulAut V)} (hKs : IsSimpleGroup ↥K) {U : Subgroup V}
    (hKU : ∀ k ∈ K, ∀ u ∈ U, k u ∈ U) {t : MulAut V} (htK : t ∈ K) (ht1 : t ≠ 1)
    (ht : ∀ u ∈ U, t u = u) : ∀ k ∈ K, ∀ u ∈ U, k u = u := by
  have := triv_normal K U hKU
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (triv K U hKU) with h | h
  · exfalso
    have hmem : (⟨t, htK⟩ : ↥K) ∈ triv K U hKU := ht
    rw [h, Subgroup.mem_bot] at hmem
    exact ht1 (congrArg Subtype.val hmem)
  · intro k hk u hu
    have hmem : (⟨k, hk⟩ : ↥K) ∈ triv K U hKU := by rw [h]; trivial
    exact hmem u hu

end Comm

section Irr

variable {V : Type*} [CommGroup V]

theorem apply_mem_fixed_of_comm {F : Subgroup (MulAut V)} {k : MulAut V}
    (hk : ∀ f ∈ F, f * k = k * f) {I : Subgroup V} (hkI : ∀ u ∈ I, k u ∈ I) {u : V}
    (hu : u ∈ XMod.fixed ↥F I) : k u ∈ XMod.fixed ↥F I := by
  refine ⟨hkI u hu.1, fun f => ?_⟩
  have h1 := hu.2 f
  rw [Subgroup.smul_def, MulAut.smul_def] at h1 ⊢
  rw [apply_comm (hk f f.2), h1]

theorem triv_quot_of_involution (hV2 : ∀ v : V, v ^ 2 = 1) {F : Subgroup (MulAut V)}
    {t : MulAut V} (ht : ∀ f ∈ F, f * t = t * f) (ht2 : t ^ 2 = 1)
    (hI : commV F ∈ IrrPlus F ⊤) : ∀ u ∈ commV F, t u * u⁻¹ ∈ XMod.fixed ↥F (commV F) := by
  obtain ⟨-, hinv, -, hlt, hirr⟩ := hI
  set I := commV F with hIdef
  set C := XMod.fixed ↥F I with hC
  have htI : ∀ u ∈ I, t u ∈ I := fun u hu => apply_mem_commV_of_comm ht hu
  have htC : ∀ u ∈ C, t u ∈ C := fun u hu => apply_mem_fixed_of_comm ht htI hu
  let J : Subgroup V :=
    { carrier := {u | u ∈ I ∧ t u * u⁻¹ ∈ C}
      one_mem' := ⟨one_mem _, by rw [map_one, inv_one, mul_one]; exact one_mem _⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        have e : t (a * b) * (a * b)⁻¹ = (t a * a⁻¹) * (t b * b⁻¹) := by
          rw [map_mul, mul_inv, mul_mul_mul_comm]
        rw [e]
        exact mul_mem ha.2 hb.2⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        have e : t a⁻¹ * a⁻¹⁻¹ = (t a * a⁻¹)⁻¹ := by
          rw [map_inv, inv_inv, mul_inv, inv_inv, mul_comm]
        rw [e]
        exact inv_mem ha.2⟩ }
  have hJinv : XMod.IsInv ↥F J := by
    intro f u hu
    refine ⟨hinv f u hu.1, ?_⟩
    have h1 := (XMod.isInv_fixed (A := ↥F) I) f _ hu.2
    rw [Subgroup.smul_def, MulAut.smul_def, map_mul, map_inv] at h1
    rw [Subgroup.smul_def, MulAut.smul_def, ← apply_comm (ht f f.2)]
    exact h1
  have hCJ : C ≤ J := fun u hu => ⟨hu.1, mul_mem (htC u hu) (inv_mem hu)⟩
  have hJI : J ≤ I := fun u hu => hu.1
  have hall : ∀ w ∈ I, t w * w⁻¹ ∈ J := by
    intro w hw
    refine ⟨mul_mem (htI w hw) (inv_mem hw), ?_⟩
    have htt : t (t w) = w := by
      rw [← MulAut.mul_apply, ← pow_two, ht2, MulAut.one_apply]
    have h1 : t (t w * w⁻¹) * (t w * w⁻¹)⁻¹ = 1 := by
      rw [map_mul, map_inv, htt, mul_inv_rev, inv_inv, ← pow_two, hV2]
    rw [h1]
    exact one_mem _
  rcases hirr J hJinv hCJ hJI with h | h
  · exfalso
    apply hlt.2
    intro w hw
    rw [← h]
    exact ⟨hw, h ▸ hall w hw⟩
  · intro u hu
    exact (h ▸ hu : u ∈ J).2

theorem triv_of_irrPlus (hV2 : ∀ v : V, v ^ 2 = 1) {F K : Subgroup (MulAut V)}
    (hFK : ∀ f ∈ F, ∀ k ∈ K, f * k = k * f) (hKs : IsSimpleGroup ↥K) {t : MulAut V}
    (htK : t ∈ K) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (hI : commV F ∈ IrrPlus F ⊤) :
    ∀ k ∈ K, ∀ u ∈ commV F, k u = u := by
  set I := commV F with hIdef
  set C := XMod.fixed ↥F I with hC
  have hkI : ∀ k ∈ K, ∀ u ∈ I, k u ∈ I := fun k hk u hu =>
    apply_mem_commV_of_comm (fun f hf => hFK f hf k hk) hu
  let D : Subgroup ↥K :=
    { carrier := {k | ∀ u ∈ I, (k : MulAut V) u * u⁻¹ ∈ C}
      one_mem' := fun u _ => by
        show (1 : MulAut V) u * u⁻¹ ∈ C
        rw [MulAut.one_apply, mul_inv_cancel]
        exact one_mem _
      mul_mem' := fun {a b} ha hb u hu => by
        show (a : MulAut V) ((b : MulAut V) u) * u⁻¹ ∈ C
        have e : (a : MulAut V) ((b : MulAut V) u) * u⁻¹ =
            ((a : MulAut V) ((b : MulAut V) u) * ((b : MulAut V) u)⁻¹) *
              ((b : MulAut V) u * u⁻¹) := by group
        rw [e]
        exact mul_mem (ha _ (hkI _ b.2 u hu)) (hb u hu)
      inv_mem' := fun {a} ha u hu => by
        show (a : MulAut V)⁻¹ u * u⁻¹ ∈ C
        have hw := hkI _ (inv_mem a.2) u hu
        have h1 := ha _ hw
        rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply] at h1
        have e : (a : MulAut V)⁻¹ u * u⁻¹ = (u * ((a : MulAut V)⁻¹ u)⁻¹)⁻¹ := by
          rw [mul_inv, inv_inv, mul_comm]
        rw [e]
        exact inv_mem h1 }
  have hDn : D.Normal := by
    refine ⟨fun k hk g u hu => ?_⟩
    show ((g * k * g⁻¹ : ↥K) : MulAut V) u * u⁻¹ ∈ C
    have hw := hkI _ (inv_mem g.2) u hu
    have h1 := apply_mem_fixed_of_comm (fun f hf => hFK f hf g g.2)
      (fun v hv => hkI g g.2 v hv) (hk _ hw)
    rw [map_mul, map_inv, apply_inv_apply] at h1
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply] using h1
  have htD : (⟨t, htK⟩ : ↥K) ∈ D :=
    triv_quot_of_involution hV2 (fun f hf => hFK f hf t htK) ht2 hI
  have hDtop : D = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D with h | h
    · exfalso
      rw [h, Subgroup.mem_bot] at htD
      exact ht1 (congrArg Subtype.val htD)
    · exact h
  obtain ⟨-, -, hcomm, -, -⟩ := hI
  intro k hk u hu
  have hkD : (⟨k, hk⟩ : ↥K) ∈ D := by rw [hDtop]; trivial
  rw [← hcomm] at hu
  induction hu using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨f, l, hl, rfl⟩ := hw
    have hc := hkD l hl
    set c := k l * l⁻¹ with hcdef
    have hkl : k l = c * l := by rw [hcdef, inv_mul_cancel_right]
    have hfc : (f : MulAut V) c = c := by
      have := hc.2 f
      rwa [Subgroup.smul_def, MulAut.smul_def] at this
    rw [Subgroup.smul_def, MulAut.smul_def, map_mul, map_inv,
      ← apply_comm (hFK f f.2 k hk), hkl, map_mul, hfc]
    calc c * (f : MulAut V) l * (c * l)⁻¹ = c * (f : MulAut V) l * (l⁻¹ * c⁻¹) := by
          rw [mul_inv_rev]
      _ = (f : MulAut V) l * l⁻¹ := by
          rw [mul_comm c, mul_comm l⁻¹ c⁻¹, ← mul_assoc, mul_assoc _ c c⁻¹, mul_inv_cancel,
            mul_one]
  | one => exact map_one k
  | mul a b _ _ ha hb => rw [map_mul, ha, hb]
  | inv a _ ha => rw [map_inv, ha]

end Irr

section TwoIrr

variable {V : Type*} [CommGroup V]

theorem eq_of_le_of_two_irr {F : Subgroup (MulAut V)} {U U₁ U₂ : Subgroup V}
    (hsup : U₁ ⊔ U₂ = U) (h₁ : XMod.IsIrr ↥F U₁)
    (h₂ : XMod.IsIrr ↥F U₂) {W W' : Subgroup V} (hW : XMod.IsInv ↥F W)
    (hW' : XMod.IsInv ↥F W') (hWU : W ≤ U) (hWne : W ≠ U) (hW'W : W' ≤ W) (hW'ne : W' ≠ ⊥) :
    W' = W := by
  have hcases : ∀ {P Ui : Subgroup V}, XMod.IsIrr ↥F Ui → XMod.IsInv ↥F P →
      P ⊓ Ui = ⊥ ∨ Ui ≤ P := by
    intro P Ui hi hP
    rcases hi.2.2 (P ⊓ Ui) (hP.inf hi.1) bot_le inf_le_right with h | h
    · exact Or.inl h
    · exact Or.inr (h ▸ inf_le_left)
  have hWU' : ∀ {Ui Uj : Subgroup V}, Ui ⊔ Uj = U → Ui ≤ W → Uj ≤ W → False := by
    intro Ui Uj hij hi hj
    exact hWne (le_antisymm hWU (hij ▸ sup_le hi hj))
  rcases hcases h₁ hW' with h1 | h1
  ·
    rcases hcases h₂ ((hW'.sup h₁.1)) with h2 | h2
    · exfalso
      apply hW'ne
      rw [eq_bot_iff]
      intro w hw
      have hwU : w ∈ U₁ ⊔ U₂ := hsup ▸ hWU (hW'W hw)
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hwU
      have hb1 : b ∈ (W' ⊔ U₁) ⊓ U₂ := ⟨by
        have : b = a⁻¹ * (a * b) := by group
        rw [this]
        exact (W' ⊔ U₁).mul_mem (Subgroup.mem_sup_right (U₁.inv_mem ha))
          (Subgroup.mem_sup_left hw), hb⟩
      rw [h2, Subgroup.mem_bot] at hb1
      rw [hb1, mul_one] at hw ⊢
      have : a ∈ W' ⊓ U₁ := ⟨hw, ha⟩
      rwa [h1] at this
    · rcases hcases h₁ hW with h3 | h3
      · refine le_antisymm hW'W fun x hx => ?_
        have hxU : x ∈ U₁ ⊔ U₂ := hsup ▸ hWU hx
        obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hxU
        obtain ⟨w', hw', a', ha', hb'⟩ := Subgroup.mem_sup.1 (h2 hb)
        have hxw : a * b * w'⁻¹ ∈ W ⊓ U₁ := ⟨W.mul_mem hx (W.inv_mem (hW'W hw')), by
          rw [← hb']
          have : a * (w' * a') * w'⁻¹ = a * a' := by
            rw [mul_comm w' a', ← mul_assoc, mul_inv_cancel_right]
          rw [this]
          exact U₁.mul_mem ha ha'⟩
        rw [h3, Subgroup.mem_bot, mul_inv_eq_one] at hxw
        rw [hxw]
        exact hw'
      · exact (hWU' hsup h3 (h2.trans (sup_le hW'W h3))).elim
  ·
    rcases hcases h₂ hW with h3 | h3
    · have hWeq : W = U₁ := by
        refine le_antisymm (fun x hx => ?_) (h1.trans hW'W)
        have hxU : x ∈ U₁ ⊔ U₂ := hsup ▸ hWU hx
        obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hxU
        have hb' : b ∈ W ⊓ U₂ := ⟨by
          have : b = a⁻¹ * (a * b) := by group
          rw [this]
          exact W.mul_mem (W.inv_mem (h1.trans hW'W ha)) hx, hb⟩
        rw [h3, Subgroup.mem_bot] at hb'
        rw [hb', mul_one]
        exact ha
      exact le_antisymm hW'W (hWeq ▸ h1)
    · exact (hWU' hsup (h1.trans hW'W) h3).elim

theorem triv_of_sum_two_irr (hV2 : ∀ v : V, v ^ 2 = 1) {F K : Subgroup (MulAut V)}
    (hFK : ∀ f ∈ F, ∀ k ∈ K, f * k = k * f) (hKs : IsSimpleGroup ↥K) {t : MulAut V}
    (htK : t ∈ K) (ht4 : t ^ 4 = 1) (ht2 : t ^ 2 ≠ 1) {U₁ U₂ : Subgroup V}
    (hsup : U₁ ⊔ U₂ = commV F) (h₁ : XMod.IsIrr ↥F U₁)
    (h₂ : XMod.IsIrr ↥F U₂) : ∀ k ∈ K, ∀ u ∈ commV F, k u = u := by
  have hkU : ∀ k ∈ K, ∀ u ∈ commV F, k u ∈ commV F := fun k hk u hu =>
    apply_mem_commV_of_comm (fun f hf => hFK f hf k hk) hu
  have hUinv : XMod.IsInv ↥F (commV F) := hsup ▸ h₁.1.sup h₂.1
  have hsK : t ^ 2 ∈ K := pow_mem htK 2
  have hs2 : t ^ 2 * t ^ 2 = 1 := by rw [← pow_add, ht4]
  refine triv_of_mem hKs hkU hsK ht2 ?_
  have htF : ∀ f ∈ F, f * t = t * f := fun f hf => hFK f hf t htK
  have hsF : ∀ f ∈ F, f * t ^ 2 = t ^ 2 * f := fun f hf => hFK f hf _ hsK
  have hinv : ∀ v : V, v⁻¹ = v := fun v => by rw [inv_eq_iff_mul_eq_one, ← pow_two, hV2]
  have hNN : ∀ u : V, t (t u * u⁻¹) * (t u * u⁻¹)⁻¹ = (t ^ 2) u * u⁻¹ := by
    intro u
    rw [map_mul, map_inv, mul_inv, inv_inv, hinv (t u), pow_two, MulAut.mul_apply, hinv u,
      mul_assoc, ← mul_assoc (t u) (t u) u, ← pow_two, hV2, one_mul]
  let fixIn : MulAut V → Subgroup V := fun g =>
    { carrier := {u | u ∈ commV F ∧ g u = u}
      one_mem' := ⟨one_mem _, map_one g⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [map_inv, ha.2]⟩ }
  let commIn : Subgroup V :=
    { carrier := {w | ∃ u ∈ commV F, (t ^ 2) u * u⁻¹ = w}
      one_mem' := ⟨1, one_mem _, by rw [map_one, inv_one, mul_one]⟩
      mul_mem' := fun {a b} ⟨u, hu, hua⟩ ⟨v, hv, hvb⟩ => ⟨u * v, mul_mem hu hv, by
        rw [← hua, ← hvb, map_mul, mul_inv, mul_mul_mul_comm]⟩
      inv_mem' := fun {a} ⟨u, hu, hua⟩ => ⟨u⁻¹, inv_mem hu, by
        rw [← hua, map_inv, inv_inv, mul_inv, inv_inv, mul_comm]⟩ }
  have hfixInv : ∀ g : MulAut V, (∀ f ∈ F, f * g = g * f) → XMod.IsInv ↥F (fixIn g) := by
    intro g hg f u hu
    refine ⟨hUinv f u hu.1, ?_⟩
    show g (f • u) = f • u
    rw [Subgroup.smul_def, MulAut.smul_def, ← apply_comm (hg f f.2), hu.2]
  have hcommInv : XMod.IsInv ↥F commIn := by
    rintro f _ ⟨u, hu, rfl⟩
    refine ⟨(f : MulAut V) u, hUinv f u hu, ?_⟩
    rw [Subgroup.smul_def, MulAut.smul_def, map_mul, map_inv, apply_comm (hsF f f.2)]
  by_contra hcon
  push Not at hcon
  obtain ⟨u₀, hu₀, hsu₀⟩ := hcon
  have hCsU : fixIn (t ^ 2) ≤ commV F := fun u hu => hu.1
  have hCsne : fixIn (t ^ 2) ≠ commV F := fun h => hsu₀ (h ▸ hu₀ : u₀ ∈ fixIn (t ^ 2)).2
  have hIsCs : commIn ≤ fixIn (t ^ 2) := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨mul_mem (hkU _ hsK u hu) (inv_mem hu), ?_⟩
    have hss : (t ^ 2) ((t ^ 2) u) = u := by
      rw [← MulAut.mul_apply, hs2, MulAut.one_apply]
    rw [map_mul, map_inv, hss, hinv ((t ^ 2) u), hinv u, mul_comm]
  have hIsne : commIn ≠ ⊥ := by
    intro hbot
    have hmem : (t ^ 2) u₀ * u₀⁻¹ ∈ commIn := ⟨u₀, hu₀, rfl⟩
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hsu₀ hmem
  have hIs : commIn = fixIn (t ^ 2) :=
    eq_of_le_of_two_irr hsup h₁ h₂ (hfixInv _ hsF) hcommInv hCsU hCsne hIsCs hIsne
  have hCtCs : fixIn t ≤ fixIn (t ^ 2) := fun u hu =>
    ⟨hu.1, by rw [pow_two, MulAut.mul_apply, hu.2, hu.2]⟩
  have hCtne : fixIn t ≠ ⊥ := by
    intro hbot
    have hNinj : ∀ u ∈ commV F, t u * u⁻¹ = 1 → u = 1 := fun u hu h => by
      have hu' : u ∈ fixIn t := ⟨hu, by rwa [mul_inv_eq_one] at h⟩
      rw [hbot] at hu'
      exact hu'
    apply hIsne
    rw [eq_bot_iff, hIs]
    intro u hu
    have h1 : t (t u * u⁻¹) * (t u * u⁻¹)⁻¹ = 1 := by
      rw [hNN, hu.2, mul_inv_cancel]
    exact hNinj u hu.1 (hNinj _ (mul_mem (hkU t htK u hu.1) (inv_mem hu.1)) h1)
  have hCt : fixIn t = fixIn (t ^ 2) :=
    eq_of_le_of_two_irr hsup h₁ h₂ (hfixInv _ hsF) (hfixInv t htF) hCsU hCsne hCtCs hCtne
  have h1 : (t ^ 2) u₀ * u₀⁻¹ ∈ fixIn t := hCt ▸ hIs ▸ ⟨u₀, hu₀, rfl⟩
  have hw : t u₀ * u₀⁻¹ ∈ commV F := mul_mem (hkU t htK _ hu₀) (inv_mem hu₀)
  have h2 : (t ^ 2) (t u₀ * u₀⁻¹) * (t u₀ * u₀⁻¹)⁻¹ = 1 := by
    rw [← hNN (t u₀ * u₀⁻¹), hNN u₀, h1.2, mul_inv_cancel]
  have h3 : t u₀ * u₀⁻¹ ∈ fixIn t := hCt ▸ ⟨hw, by rwa [mul_inv_eq_one] at h2⟩
  have h4 : t (t u₀ * u₀⁻¹) * (t u₀ * u₀⁻¹)⁻¹ = 1 := by rw [h3.2, mul_inv_cancel]
  rw [hNN u₀, mul_inv_eq_one] at h4
  exact hsu₀ h4

end TwoIrr

section Card

variable {V : Type*} [CommGroup V] [Finite V]

theorem triv_of_card {R K : Subgroup (MulAut V)} (hRK : ∀ r ∈ R, ∀ k ∈ K, r * k = k * r)
    (hKs : IsSimpleGroup ↥K) (hcard : (Nat.card (commV R)).factorial < Nat.card K) :
    ∀ k ∈ K, ∀ u ∈ commV R, k u = u := by
  have hkU : ∀ k ∈ K, ∀ u ∈ commV R, k u ∈ commV R := fun k hk u hu =>
    apply_mem_commV_of_comm (fun r hr => hRK r hr k hk) hu
  let φ : ↥K →* Equiv.Perm ↥(commV R) :=
    { toFun := fun k =>
        { toFun := fun u => ⟨(k : MulAut V) u, hkU _ k.2 _ u.2⟩
          invFun := fun u => ⟨(k : MulAut V)⁻¹ u, hkU _ (inv_mem k.2) _ u.2⟩
          left_inv := fun u => Subtype.ext (inv_apply_apply _ _)
          right_inv := fun u => Subtype.ext (apply_inv_apply _ _) }
      map_one' := by ext u; rfl
      map_mul' := fun a b => by ext u; rfl }
  have hker : φ.ker = triv K (commV R) hkU := by
    ext k
    rw [MonoidHom.mem_ker]
    constructor
    · intro h u hu
      exact congrArg Subtype.val (DFunLike.congr_fun h ⟨u, hu⟩)
    · intro h
      ext u
      exact h u u.2
  have := triv_normal K (commV R) hkU
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (triv K (commV R) hkU) with h | h
  · exfalso
    have hinj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, hker, h]
    have h1 := Nat.card_le_card_of_injective φ hinj
    rw [Nat.card_perm] at h1
    omega
  · intro k hk u hu
    have hmem : (⟨k, hk⟩ : ↥K) ∈ triv K (commV R) hkU := by rw [h]; trivial
    exact hmem u hu

end Card

end CFSG.Quasithin.H13.U3.P2
