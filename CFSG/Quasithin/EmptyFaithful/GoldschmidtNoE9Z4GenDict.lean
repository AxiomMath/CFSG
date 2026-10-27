module

public import CFSG.Quasithin.EmptyFaithful.S14612ED

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits
  CFSG.Quasithin.C1Pack CFSG.Quasithin.S1417
open scoped commutatorElement

namespace NoE9Z4GenBridge

section Proj

variable {W : Type*} [CommGroup W] {K F : Subgroup W}

theorem exists_proj (hKF : K ⊓ F = ⊥) (hsplit : ∀ w : W, ∃ a ∈ K, ∃ c ∈ F, w = a * c) :
    ∃ π : W →* K, ∀ (w : W) (a : K) (c : W), c ∈ F → w = (a : W) * c → π w = a := by
  classical
  have huniq : ∀ (a a' : K) (c c' : W), c ∈ F → c' ∈ F → (a : W) * c = (a' : W) * c' →
      a = a' := by
    intro a a' c c' hc hc' h
    have h1 : (a' : W)⁻¹ * (a : W) = c' * c⁻¹ := by
      calc (a' : W)⁻¹ * (a : W) = (a' : W)⁻¹ * ((a : W) * c) * c⁻¹ := by group
        _ = (a' : W)⁻¹ * ((a' : W) * c') * c⁻¹ := by rw [h]
        _ = c' * c⁻¹ := by group
    have hK1 : (a' : W)⁻¹ * (a : W) ∈ K := K.mul_mem (K.inv_mem a'.2) a.2
    have hF1 : (a' : W)⁻¹ * (a : W) ∈ F := h1 ▸ F.mul_mem hc' (F.inv_mem hc)
    have h2 : (a' : W)⁻¹ * (a : W) ∈ K ⊓ F := ⟨hK1, hF1⟩
    rw [hKF, Subgroup.mem_bot] at h2
    exact Subtype.ext (inv_mul_eq_one.mp h2).symm
  let f : W → K := fun w =>
    ⟨Classical.choose (hsplit w), (Classical.choose_spec (hsplit w)).1⟩
  have hf : ∀ (w : W) (a : K) (c : W), c ∈ F → w = (a : W) * c → f w = a := by
    intro w a c hc hw
    obtain ⟨-, c₀, hc₀, hw₀⟩ := Classical.choose_spec (hsplit w)
    exact huniq _ _ c₀ c hc₀ hc (by rw [← hw₀, hw])
  refine ⟨{ toFun := f, map_one' := hf 1 1 1 F.one_mem (by simp), map_mul' := ?_ }, hf⟩
  intro w w'
  obtain ⟨a, ha, c, hc, rfl⟩ := hsplit w
  obtain ⟨a', ha', c', hc', rfl⟩ := hsplit w'
  have e1 : f (a * c) = ⟨a, ha⟩ := hf _ ⟨a, ha⟩ c hc rfl
  have e2 : f (a' * c') = ⟨a', ha'⟩ := hf _ ⟨a', ha'⟩ c' hc' rfl
  have e3 : f (a * c * (a' * c')) = ⟨a, ha⟩ * ⟨a', ha'⟩ :=
    hf _ (⟨a, ha⟩ * ⟨a', ha'⟩) (c * c') (F.mul_mem hc hc') (by
      rw [mul_mul_mul_comm]; rfl)
  show f (a * c * (a' * c')) = f (a * c) * f (a' * c')
  rw [e1, e2, e3]

end Proj

section Cls

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}
variable (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)

open Classical in
noncomputable def clsW (u : G) : UMod h :=
  if hu : u ∈ conjClosure (VZ T M) H then
    IntMod.mk h.isElemAbelian_tilde
      ⟨secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) ⟨u, U_le_normalizer h hu⟩, secMk_mem_secImg hu⟩
  else 1

variable {h}

theorem valW_clsW {u : G} (hu : u ∈ conjClosure (VZ T M) H) :
    valW h (clsW h u) = secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T) ⟨u, U_le_normalizer h hu⟩ := by
  simp only [clsW, hu, ↓reduceDIte]
  rfl

theorem clsW_mul {u u' : G} (hu : u ∈ conjClosure (VZ T M) H)
    (hu' : u' ∈ conjClosure (VZ T M) H) : clsW h (u * u') = clsW h u * clsW h u' := by
  apply valW_injective h
  rw [valW_clsW ((conjClosure (VZ T M) H).mul_mem hu hu'), map_mul, valW_clsW hu, valW_clsW hu',
    ← map_mul]
  rfl

theorem clsW_eq_one_iff {u : G} (hu : u ∈ conjClosure (VZ T M) H) :
    clsW h u = 1 ↔ u ∈ quasithinOmegaOneCenter T := by
  constructor
  · intro h1
    have h2 := congrArg (valW h) h1
    rw [valW_clsW hu, map_one] at h2
    exact secMk_eq_one_iff.mp h2
  · intro h1
    apply valW_injective h
    rw [valW_clsW hu, map_one]
    exact secMk_eq_one_iff.mpr h1

theorem clsW_one : clsW h 1 = 1 :=
  (clsW_eq_one_iff (h := h) (conjClosure (VZ T M) H).one_mem).mpr
    (quasithinOmegaOneCenter T).one_mem

theorem clsW_inv {u : G} (hu : u ∈ conjClosure (VZ T M) H) :
    clsW h u⁻¹ = (clsW h u)⁻¹ := by
  have h1 := clsW_mul (h := h) hu ((conjClosure (VZ T M) H).inv_mem hu)
  rw [mul_inv_cancel, clsW_one] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

theorem clsW_conj (x : ↥H) {u : G} (hu : u ∈ conjClosure (VZ T M) H) :
    clsW h ((x : G) * u * (x : G)⁻¹) = rhoH h x (clsW h u) := by
  have hxu : (x : G) * u * (x : G)⁻¹ ∈ conjClosure (VZ T M) H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ x.2) u).mp hu
  apply valW_injective h
  rw [valW_clsW hxu]
  show _ = (rhoH h x (clsW h u)).val
  rw [rhoH_val]
  show _ = secMk _ _ (Subgroup.inclusion h.H_normalizes_V₁ x) * valW h (clsW h u) *
    (secMk _ _ (Subgroup.inclusion h.H_normalizes_V₁ x))⁻¹
  rw [valW_clsW hu, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem clsW_comm (x : ↥H) {u : G} (hu : u ∈ conjClosure (VZ T M) H) :
    clsW h ⁅u, (x : G)⁆ = clsW h u * (rhoH h x (clsW h u))⁻¹ := by
  have hU := conjClosure (VZ T M) H
  have hu' : u⁻¹ ∈ conjClosure (VZ T M) H := (conjClosure (VZ T M) H).inv_mem hu
  have hxu : (x : G) * u⁻¹ * (x : G)⁻¹ ∈ conjClosure (VZ T M) H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ x.2) u⁻¹).mp hu'
  have e : ⁅u, (x : G)⁆ = u * ((x : G) * u⁻¹ * (x : G)⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, clsW_mul hu hxu, clsW_conj x hu', clsW_inv hu, map_inv]

theorem exists_cls
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    (hinf : kOf (rhoH h) ⊓ fixV (rhoH h).range = ⊥) :
    ∃ (cls : G → ↥(kOf (rhoH h))) (U0 : Subgroup G),
      U0 ≤ conjClosure (VZ T M) H ∧ quasithinOmegaOneCenter T ≤ U0 ∧
      (∀ x ∈ H, ∀ u ∈ U0, x * u * x⁻¹ ∈ U0) ∧
      (∀ u ∈ conjClosure (VZ T M) H, ∀ u' ∈ conjClosure (VZ T M) H,
        cls (u * u') = cls u * cls u') ∧
      (∀ u ∈ U0, (cls u = 1 ↔ u ∈ quasithinOmegaOneCenter T)) ∧
      (∀ x : ↥H, ∀ u ∈ conjClosure (VZ T M) H,
        cls ((x : G) * u * (x : G)⁻¹) = resBeta (rhoH h) x (cls u)) ∧
      (∀ k : ↥(kOf (rhoH h)), ∃ u ∈ U0, cls u = k) ∧
      (∀ u ∈ conjClosure (VZ T M) H, ∀ x ∈ H, ⁅u, x⁆ ∈ U0) ∧
      (∀ u ∈ conjClosure (VZ T M) H, cls u = 1 → ∀ x ∈ H,
        ⁅u, x⁆ ∈ quasithinOmegaOneCenter T) := by
  obtain ⟨π, hπ⟩ := exists_proj hinf hsplit
  have hπK : ∀ a : ↥(kOf (rhoH h)), π (a : UMod h) = a := fun a =>
    hπ _ a 1 (one_mem _) (by simp)
  have hρK : ∀ (x : ↥H) (a : UMod h), a ∈ kOf (rhoH h) → rhoH h x a ∈ kOf (rhoH h) :=
    fun x a ha => (resBeta (rhoH h) x ⟨a, ha⟩).2
  have hπρ : ∀ (x : ↥H) (w : UMod h), π (rhoH h x w) = resBeta (rhoH h) x (π w) := by
    intro x w
    obtain ⟨a, ha, c, hc, rfl⟩ := hsplit w
    have h1 : π (a * c) = ⟨a, ha⟩ := hπ _ ⟨a, ha⟩ c hc rfl
    have h2 : rhoH h x c = c := hc (rhoH h x) ⟨x, rfl⟩
    have h3 : rhoH h x (a * c) =
        ((resBeta (rhoH h) x ⟨a, ha⟩ : ↥(kOf (rhoH h))) : UMod h) * c := by
      rw [map_mul, h2]
      rfl
    rw [h1, h3]
    exact hπ _ _ c hc rfl
  have hkey : ∀ (x : ↥H) (w : UMod h), w * (rhoH h x w)⁻¹ ∈ kOf (rhoH h) := by
    intro x w
    obtain ⟨a, ha, c, hc, rfl⟩ := hsplit w
    have h2 : rhoH h x c = c := hc (rhoH h x) ⟨x, rfl⟩
    have e : a * c * (rhoH h x (a * c))⁻¹ = a * (rhoH h x a)⁻¹ := by
      rw [map_mul, h2, mul_inv_rev]
      group
    rw [e]
    exact mul_mem ha (inv_mem (hρK x a ha))
  let U0 : Subgroup G :=
    { carrier := {u | u ∈ conjClosure (VZ T M) H ∧ clsW h u ∈ kOf (rhoH h)}
      one_mem' := ⟨one_mem _, by rw [clsW_one]; exact one_mem _⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [clsW_mul ha.1 hb.1]; exact mul_mem ha.2 hb.2⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        rw [clsW_inv ha.1]; exact inv_mem ha.2⟩ }
  have hU0mem : ∀ u : G, u ∈ U0 ↔ u ∈ conjClosure (VZ T M) H ∧ clsW h u ∈ kOf (rhoH h) :=
    fun u => Iff.rfl
  have hUcomm : ∀ u ∈ conjClosure (VZ T M) H, ∀ x ∈ H, ⁅u, x⁆ ∈ conjClosure (VZ T M) H := by
    intro u hu x hx
    have e : ⁅u, x⁆ = u * (x * u⁻¹ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    have hxu : x * u⁻¹ * x⁻¹ ∈ conjClosure (VZ T M) H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ hx) u⁻¹).mp
        ((conjClosure (VZ T M) H).inv_mem hu)
    rw [e]
    exact mul_mem hu hxu
  refine ⟨fun u => π (clsW h u), U0, fun u hu => ((hU0mem u).mp hu).1, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro u hu
    have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
    have hVU : VZ T M ≤ conjClosure (VZ T M) H := le_conjClosure _ _
    have huU : u ∈ conjClosure (VZ T M) H := hVU (hZV hu)
    refine (hU0mem u).mpr ⟨huU, ?_⟩
    rw [(clsW_eq_one_iff huU).mpr hu]
    exact one_mem _
  · intro x hx u hu
    obtain ⟨huU, huK⟩ := (hU0mem u).mp hu
    have hxu : x * u * x⁻¹ ∈ conjClosure (VZ T M) H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ hx) u).mp huU
    refine (hU0mem _).mpr ⟨hxu, ?_⟩
    have h' : clsW h (x * u * x⁻¹) = rhoH h ⟨x, hx⟩ (clsW h u) := clsW_conj ⟨x, hx⟩ huU
    rw [h']
    exact hρK _ _ huK
  · intro u hu u' hu'
    show π (clsW h (u * u')) = π (clsW h u) * π (clsW h u')
    rw [clsW_mul hu hu', map_mul]
  · intro u hu
    obtain ⟨huU, huK⟩ := (hU0mem u).mp hu
    have e : π (clsW h u) = ⟨clsW h u, huK⟩ := hπK ⟨clsW h u, huK⟩
    show π (clsW h u) = 1 ↔ _
    rw [e, ← clsW_eq_one_iff (h := h) huU]
    exact ⟨fun h1 => congrArg Subtype.val h1, fun h1 => Subtype.ext h1⟩
  · intro x u hu
    show π (clsW h ((x : G) * u * (x : G)⁻¹)) = resBeta (rhoH h) x (π (clsW h u))
    rw [clsW_conj x hu, hπρ]
  · intro k
    have hmem : (k : UMod h).val ∈ secImg (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H) := IntMod.val_mem _
    obtain ⟨x, hxU, hxk⟩ := mem_secImg.mp hmem
    have hcl : clsW h (x : G) = (k : UMod h) := by
      apply valW_injective h
      rw [valW_clsW hxU]
      exact hxk
    refine ⟨x, (hU0mem _).mpr ⟨hxU, by rw [hcl]; exact k.2⟩, ?_⟩
    show π (clsW h x) = k
    rw [hcl]
    exact hπK k
  · intro u hu x hx
    refine (hU0mem _).mpr ⟨hUcomm u hu x hx, ?_⟩
    rw [clsW_comm ⟨x, hx⟩ hu]
    exact hkey ⟨x, hx⟩ (clsW h u)
  · intro u hu hcls x hx
    rw [← clsW_eq_one_iff (h := h) (hUcomm u hu x hx), clsW_comm ⟨x, hx⟩ hu]
    obtain ⟨a, ha, c, hc, hw⟩ := hsplit (clsW h u)
    have h1 : π (clsW h u) = ⟨a, ha⟩ := hπ _ ⟨a, ha⟩ c hc hw
    have h2 : a = 1 := congrArg Subtype.val (h1.symm.trans hcls)
    have hw' : clsW h u = c := by rw [hw, h2, one_mul]
    have h3 : rhoH h ⟨x, hx⟩ (clsW h u) = clsW h u := by
      rw [hw']
      exact hc _ ⟨⟨x, hx⟩, rfl⟩
    rw [h3, mul_inv_cancel]

end Cls

end NoE9Z4GenBridge

end CFSG.Quasithin
