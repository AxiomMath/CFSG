module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Data.Fin.VecNotation

public section

namespace CFSG.Quasithin

open MulAction Subgroup

@[expose] def SharpOn {G Ω : Type*} [Group G] [MulAction G Ω] (Γ : Subgroup G) (Y : Set Ω)
    (k : ℕ) : Prop :=
  ∀ a b : Fin k → Ω, (∀ i, a i ∈ Y) → (∀ i, b i ∈ Y) → Function.Injective a →
    Function.Injective b → ∃! g : G, g ∈ Γ ∧ ∀ i, g • a i = b i

theorem SharpOn.succ {G Ω : Type*} [Group G] [MulAction G Ω] (Γ S : Subgroup G) (Y : Set Ω)
    (y₀ : Ω) (k : ℕ) (hinv : ∀ g ∈ Γ, ∀ y ∈ Y, g • y ∈ Y)
    (htrans : ∀ y ∈ Y, ∃ g ∈ Γ, g • y₀ = y) (hS : ∀ g, g ∈ S ↔ g ∈ Γ ∧ g • y₀ = y₀)
    (hk : SharpOn S (Y \ {y₀}) k) : SharpOn Γ Y (k + 1) := by
  intro a b ha hb hai hbi
  obtain ⟨h₁, hh₁, hh₁a⟩ := htrans (a 0) (ha 0)
  obtain ⟨h₂, hh₂, hh₂b⟩ := htrans (b 0) (hb 0)
  have h1a : h₁⁻¹ • a 0 = y₀ := by rw [← hh₁a, inv_smul_smul]
  have h2b : h₂⁻¹ • b 0 = y₀ := by rw [← hh₂b, inv_smul_smul]
  have hmem₁ : ∀ i : Fin k, h₁⁻¹ • a i.succ ∈ Y \ {y₀} := by
    intro i
    refine ⟨hinv _ (Γ.inv_mem hh₁) _ (ha _), ?_⟩
    intro h
    have h' : h₁⁻¹ • a i.succ = h₁⁻¹ • a 0 := by
      rw [h1a]; exact h
    exact (Fin.succ_ne_zero i) (hai (smul_left_cancel _ h'))
  have hmem₂ : ∀ i : Fin k, h₂⁻¹ • b i.succ ∈ Y \ {y₀} := by
    intro i
    refine ⟨hinv _ (Γ.inv_mem hh₂) _ (hb _), ?_⟩
    intro h
    have h' : h₂⁻¹ • b i.succ = h₂⁻¹ • b 0 := by
      rw [h2b]; exact h
    exact (Fin.succ_ne_zero i) (hbi (smul_left_cancel _ h'))
  obtain ⟨s, ⟨hsS, hs⟩, hsu⟩ := hk (fun i => h₁⁻¹ • a i.succ) (fun i => h₂⁻¹ • b i.succ) hmem₁
    hmem₂ (fun i j hij => Fin.succ_injective _ (hai (smul_left_cancel _ hij)))
    (fun i j hij => Fin.succ_injective _ (hbi (smul_left_cancel _ hij)))
  obtain ⟨hsΓ, hsfix⟩ := (hS s).1 hsS
  refine ⟨h₂ * s * h₁⁻¹, ⟨?_, ?_⟩, ?_⟩
  · exact Γ.mul_mem (Γ.mul_mem hh₂ hsΓ) (Γ.inv_mem hh₁)
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [mul_smul, mul_smul, h1a, hsfix, hh₂b]
    · have : s • (h₁⁻¹ • a j.succ) = h₂⁻¹ • b j.succ := hs j
      rw [mul_smul, mul_smul, this, smul_inv_smul]
  · rintro g ⟨hgΓ, hg⟩
    have hsg : h₂⁻¹ * g * h₁ ∈ S := by
      rw [hS]
      refine ⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hh₂) hgΓ) hh₁, ?_⟩
      rw [mul_smul, mul_smul, hh₁a, hg 0, h2b]
    have hsg' : h₂⁻¹ * g * h₁ = s := by
      refine hsu _ ⟨hsg, fun i => ?_⟩
      show (h₂⁻¹ * g * h₁) • (h₁⁻¹ • a i.succ) = h₂⁻¹ • b i.succ
      rw [mul_smul, mul_smul, smul_inv_smul, hg i.succ]
    calc g = h₂ * (h₂⁻¹ * g * h₁) * h₁⁻¹ := by group
      _ = h₂ * s * h₁⁻¹ := by rw [hsg']

structure TailCore {G : Type*} [Group G] (L K : Subgroup G) (v z r : G) : Prop where
  hKL : K ≤ L
  hv : v * v = 1
  hvK : ∀ k ∈ K, v * k * v ∈ K
  hvL : ∃ l ∈ L, v * l * v ∉ L
  hrL : r ∈ L
  hrr : r * r = 1
  hrv : r * v * r = v * r * v
  hdc : ∀ l ∈ L, l ∈ K ∨ ∃ k₁ ∈ K, ∃ k₂ ∈ K, l = k₁ * r * k₂
  hz : z * z = 1
  hzL : ∀ l ∈ L, z * l * z ∈ L
  hzn : z ∉ L
  hzv : z * v * z = v * z * v

namespace TailCore

variable {G : Type*} [Group G] {L K : Subgroup G} {v z r : G} (h : TailCore L K v z r)

include h

theorem inv_v : v⁻¹ = v := inv_eq_of_mul_eq_one_right h.hv

theorem inv_z : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.hz

theorem vrvrv : v * r * v * r * v = r := by
  calc v * r * v * r * v = (r * v * r) * r * v := by rw [h.hrv]
    _ = r * v * (r * r) * v := by group
    _ = r := by rw [h.hrr, mul_one, mul_assoc, h.hv, mul_one]

theorem conj_v_mem_or {l : G} (hl : l ∈ L) :
    v * l * v ∈ L ∨ ∃ l₁ ∈ L, ∃ l₂ ∈ L, v * l * v = l₁ * v * l₂ := by
  rcases h.hdc l hl with hK | ⟨k₁, hk₁, k₂, hk₂, rfl⟩
  · exact Or.inl (h.hKL (h.hvK l hK))
  · right
    refine ⟨v * k₁ * v * r, L.mul_mem (h.hKL (h.hvK k₁ hk₁)) h.hrL, r * (v * k₂ * v),
      L.mul_mem h.hrL (h.hKL (h.hvK k₂ hk₂)), ?_⟩
    calc v * (k₁ * r * k₂) * v = v * k₁ * (v * r * v * r * v) * k₂ * v := by
          rw [h.vrvrv]; group
      _ = v * k₁ * v * r * v * (r * (v * k₂ * v)) := by group

theorem conj_mul3 (a b c : G) :
    v * (a * b * c) * v = (v * a * v) * (v * b * v) * (v * c * v) := by
  have e : v * (a * b * c) * v⁻¹ = (v * a * v⁻¹) * (v * b * v⁻¹) * (v * c * v⁻¹) := by group
  rwa [h.inv_v] at e

theorem mem_K_of_conj_mem {l : G} (hl : l ∈ L) (hvl : v * l * v ∈ L) : l ∈ K := by
  by_contra hK
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (h.hdc l hl).resolve_left hK
  have hx : v * k₁ * v ∈ L := h.hKL (h.hvK k₁ hk₁)
  have hw : v * k₂ * v ∈ L := h.hKL (h.hvK k₂ hk₂)
  have h1 : v * r * v ∈ L := by
    have e : v * r * v = (v * k₁ * v)⁻¹ * ((v * k₁ * v) * (v * r * v) * (v * k₂ * v)) *
        (v * k₂ * v)⁻¹ := by group
    rw [e, ← h.conj_mul3]
    exact L.mul_mem (L.mul_mem (L.inv_mem hx) hvl) (L.inv_mem hw)
  have h2 : r * v * r ∈ L := by rw [h.hrv]; exact h1
  have h3 : v ∈ L := by
    have e : v = r * (r * v * r) * r := by
      calc v = (r * r) * v * (r * r) := by rw [h.hrr]; simp
        _ = r * (r * v * r) * r := by group
    rw [e]
    exact L.mul_mem (L.mul_mem h.hrL h2) h.hrL
  obtain ⟨l', hl', hnot⟩ := h.hvL
  exact hnot (L.mul_mem (L.mul_mem h3 hl') h3)

@[expose] def M : Subgroup G where
  carrier := {g | g ∈ L ∨ ∃ l₁ ∈ L, ∃ l₂ ∈ L, g = l₁ * v * l₂}
  one_mem' := Or.inl L.one_mem
  mul_mem' := by
    rintro a b (ha | ⟨a₁, ha₁, a₂, ha₂, rfl⟩) (hb | ⟨b₁, hb₁, b₂, hb₂, rfl⟩)
    · exact Or.inl (L.mul_mem ha hb)
    · exact Or.inr ⟨a * b₁, L.mul_mem ha hb₁, b₂, hb₂, by group⟩
    · exact Or.inr ⟨a₁, ha₁, a₂ * b, L.mul_mem ha₂ hb, by group⟩
    · have e : a₁ * v * a₂ * (b₁ * v * b₂) = a₁ * (v * (a₂ * b₁) * v) * b₂ := by group
      rcases h.conj_v_mem_or (L.mul_mem ha₂ hb₁) with hL | ⟨c₁, hc₁, c₂, hc₂, hc⟩
      · exact Or.inl (by rw [e]; exact L.mul_mem (L.mul_mem ha₁ hL) hb₂)
      · exact Or.inr ⟨a₁ * c₁, L.mul_mem ha₁ hc₁, c₂ * b₂, L.mul_mem hc₂ hb₂, by
          rw [e, hc]; group⟩
  inv_mem' := by
    rintro a (ha | ⟨a₁, ha₁, a₂, ha₂, rfl⟩)
    · exact Or.inl (L.inv_mem ha)
    · refine Or.inr ⟨a₂⁻¹, L.inv_mem ha₂, a₁⁻¹, L.inv_mem ha₁, ?_⟩
      rw [mul_inv_rev, mul_inv_rev, h.inv_v]; group

theorem mem_M_iff {g : G} :
    g ∈ h.M ↔ g ∈ L ∨ ∃ l₁ ∈ L, ∃ l₂ ∈ L, g = l₁ * v * l₂ := Iff.rfl

theorem L_le_M : L ≤ h.M := fun _ hg => Or.inl hg

theorem v_mem_M : v ∈ h.M := Or.inr ⟨1, L.one_mem, 1, L.one_mem, by simp⟩

theorem z_not_mem_M : z ∉ h.M := by
  rintro (hz' | ⟨l₁, hl₁, l₂, hl₂, hz'⟩)
  · exact h.hzn hz'
  · obtain ⟨l', hl', hnot⟩ := h.hvL
    have hv1 : v = l₁⁻¹ * z * l₂⁻¹ := by rw [hz']; group
    have hv2 : v = l₂ * z * l₁ := by
      have e : v⁻¹ = l₂ * z⁻¹ * l₁ := by
        rw [show z⁻¹ = (l₁ * v * l₂)⁻¹ by rw [← hz']]; group
      rwa [h.inv_v, h.inv_z] at e
    apply hnot
    have e : v * l' * v = l₁⁻¹ * (z * (l₂⁻¹ * l' * l₂) * z) * l₁ := by
      calc v * l' * v = (l₁⁻¹ * z * l₂⁻¹) * l' * (l₂ * z * l₁) := by
            rw [← hv1, ← hv2]
        _ = l₁⁻¹ * (z * (l₂⁻¹ * l' * l₂) * z) * l₁ := by group
    rw [e]
    exact L.mul_mem (L.mul_mem (L.inv_mem hl₁) (h.hzL _ (L.mul_mem (L.mul_mem (L.inv_mem hl₂) hl')
      hl₂))) hl₁

theorem mem_L_of_conj_z_mem {m : G} (hm : m ∈ h.M) (hzm : z * m * z ∈ h.M) : m ∈ L := by
  by_contra hmL
  obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := (h.mem_M_iff.1 hm).resolve_left hmL
  have e : z * v * z = (z * l₁ * z)⁻¹ * (z * (l₁ * v * l₂) * z) * (z * l₂ * z)⁻¹ := by
    have e' : z * (l₁ * v * l₂) * z = (z * l₁ * z) * (z * v * z) * (z * l₂ * z) := by
      have e'' : z * (l₁ * v * l₂) * z⁻¹ = (z * l₁ * z⁻¹) * (z * v * z⁻¹) * (z * l₂ * z⁻¹) := by
        group
      rwa [h.inv_z] at e''
    rw [e']; group
  have hzvz : z * v * z ∈ h.M := by
    rw [e]
    exact h.M.mul_mem (h.M.mul_mem (h.M.inv_mem (h.L_le_M (h.hzL _ hl₁))) hzm)
      (h.M.inv_mem (h.L_le_M (h.hzL _ hl₂)))
  apply h.z_not_mem_M
  have e2 : z = v * (z * v * z) * v := by
    calc z = (v * v) * z * (v * v) := by rw [h.hv]; simp
      _ = v * (v * z * v) * v := by group
      _ = v * (z * v * z) * v := by rw [h.hzv]
  exact (congrArg (· ∈ h.M) e2).mpr (h.M.mul_mem (h.M.mul_mem h.v_mem_M hzvz) h.v_mem_M)

@[expose] def ω₀ : G ⧸ h.M := ((1 : G) : G ⧸ h.M)

@[expose] def ω₁ : G ⧸ h.M := ((z : G) : G ⧸ h.M)

theorem smul_mk (g x : G) : g • ((x : G) : G ⧸ h.M) = ((g * x : G) : G ⧸ h.M) := rfl

theorem smul_ω₀_eq_iff (g : G) : g • h.ω₀ = h.ω₀ ↔ g ∈ h.M := by
  unfold ω₀
  rw [smul_mk, mul_one, QuotientGroup.eq, mul_one, Subgroup.inv_mem_iff]

theorem ω₁_ne_ω₀ : h.ω₁ ≠ h.ω₀ := by
  intro e
  unfold ω₁ ω₀ at e
  rw [QuotientGroup.eq, mul_one, Subgroup.inv_mem_iff] at e
  exact h.z_not_mem_M e

@[expose] def eMap : (↥L ⧸ K.subgroupOf L) → G ⧸ h.M :=
  Quotient.lift (fun l : ↥L => (((l : G) * v * z : G) : G ⧸ h.M)) (by
    intro a b hab
    have hab' : (a : ↥L)⁻¹ * b ∈ K.subgroupOf L := QuotientGroup.leftRel_apply.1 hab
    rw [Subgroup.mem_subgroupOf] at hab'
    show (QuotientGroup.mk _ : G ⧸ h.M) = QuotientGroup.mk _
    rw [QuotientGroup.eq]
    have hk : v * ((a : G)⁻¹ * (b : G)) * v ∈ K := h.hvK _ hab'

    have e : ((a : G) * v * z)⁻¹ * ((b : G) * v * z) =
        z * (v * ((a : G)⁻¹ * (b : G)) * v) * z := by
      have e' : ((a : G) * v * z)⁻¹ * ((b : G) * v * z) =
          z⁻¹ * (v⁻¹ * ((a : G)⁻¹ * (b : G)) * v) * z := by group
      rwa [h.inv_z, h.inv_v] at e'
    rw [e]
    exact h.L_le_M (h.hzL _ (h.hKL hk)))

theorem eMap_mk (l : ↥L) :
    h.eMap (QuotientGroup.mk l : ↥L ⧸ K.subgroupOf L) = (((l : G) * v * z : G) : G ⧸ h.M) := rfl

theorem eMap_smul (g : ↥L) (x : ↥L ⧸ K.subgroupOf L) :
    (g : G) • h.eMap x = h.eMap (g • x) := by
  induction x using QuotientGroup.induction_on with
  | H l =>
    change (QuotientGroup.mk ((g : G) * ((l : G) * v * z)) : G ⧸ h.M) =
      QuotientGroup.mk (((g * l : ↥L) : G) * v * z)
    rw [Subgroup.coe_mul]
    congr 1
    group

theorem v_not_mem_L : v ∉ L := by
  intro hvL
  obtain ⟨l, hl, hnot⟩ := h.hvL
  exact hnot (L.mul_mem (L.mul_mem hvL hl) hvL)

theorem key_identity (a b : ↥L) :
    ((a : G) * v * z)⁻¹ * ((b : G) * v * z) = z * (v * ((a : G)⁻¹ * (b : G)) * v) * z := by
  have e' : ((a : G) * v * z)⁻¹ * ((b : G) * v * z) =
      z⁻¹ * (v⁻¹ * ((a : G)⁻¹ * (b : G)) * v) * z := by group
  rwa [h.inv_z, h.inv_v] at e'

theorem eMap_injective : Function.Injective h.eMap := by
  intro x y hxy
  induction x using QuotientGroup.induction_on with
  | H a =>
    induction y using QuotientGroup.induction_on with
    | H b =>
      rw [eMap_mk, eMap_mk, QuotientGroup.eq, h.key_identity] at hxy
      have hkL : (a : G)⁻¹ * (b : G) ∈ L := L.mul_mem (L.inv_mem a.2) b.2
      have hm : v * ((a : G)⁻¹ * (b : G)) * v ∈ h.M :=
        h.M.mul_mem (h.M.mul_mem h.v_mem_M (h.L_le_M hkL)) h.v_mem_M
      have h2 := h.mem_K_of_conj_mem hkL (h.mem_L_of_conj_z_mem hm hxy)
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      exact h2

theorem ω₀_not_mem_range : h.ω₀ ∉ Set.range h.eMap := by
  rintro ⟨x, hx⟩
  induction x using QuotientGroup.induction_on with
  | H l =>
    rw [eMap_mk] at hx
    unfold ω₀ at hx
    rw [QuotientGroup.eq, mul_one, Subgroup.inv_mem_iff] at hx
    have hlv : (l : G) * v ∈ h.M := h.M.mul_mem (h.L_le_M l.2) h.v_mem_M
    apply h.z_not_mem_M
    have e : z = ((l : G) * v)⁻¹ * ((l : G) * v * z) := by group
    exact (congrArg (· ∈ h.M) e).mpr (h.M.mul_mem (h.M.inv_mem hlv) hx)

theorem ω₁_not_mem_range : h.ω₁ ∉ Set.range h.eMap := by
  rintro ⟨x, hx⟩
  induction x using QuotientGroup.induction_on with
  | H l =>
    rw [eMap_mk] at hx
    unfold ω₁ at hx
    rw [QuotientGroup.eq] at hx
    have e : ((l : G) * v * z)⁻¹ * z = z * (v * (l : G)⁻¹) * z := by
      have e' : ((l : G) * v * z)⁻¹ * z = z⁻¹ * (v⁻¹ * (l : G)⁻¹) * z := by group
      rwa [h.inv_z, h.inv_v] at e'
    rw [e] at hx
    have hm : v * (l : G)⁻¹ ∈ h.M := h.M.mul_mem h.v_mem_M (h.L_le_M (L.inv_mem l.2))
    have h1 := h.mem_L_of_conj_z_mem hm hx
    apply h.v_not_mem_L
    have e2 : v = (v * (l : G)⁻¹) * (l : G) := by group
    rw [e2]
    exact L.mul_mem h1 l.2

theorem orbit_eq :
    (orbit ↥h.M h.ω₁ : Set (G ⧸ h.M)) = {h.ω₁} ∪ Set.range h.eMap := by
  ext p
  constructor
  · rintro ⟨⟨m, hm⟩, rfl⟩
    rcases h.mem_M_iff.1 hm with hmL | ⟨l₁, hl₁, l₂, hl₂, rfl⟩
    · left
      show (((m * z : G)) : G ⧸ h.M) = ((z : G) : G ⧸ h.M)
      rw [QuotientGroup.eq]
      have e : (m * z)⁻¹ * z = z * m⁻¹ * z := by
        have e' : (m * z)⁻¹ * z = z⁻¹ * m⁻¹ * z := by group
        rwa [h.inv_z] at e'
      rw [e]
      exact h.L_le_M (h.hzL _ (L.inv_mem hmL))
    · right
      refine ⟨QuotientGroup.mk ⟨l₁, hl₁⟩, ?_⟩
      rw [eMap_mk]
      show (((l₁ : G) * v * z : G) : G ⧸ h.M) = (((l₁ * v * l₂ * z : G)) : G ⧸ h.M)
      rw [QuotientGroup.eq]
      have e : ((l₁ : G) * v * z)⁻¹ * (l₁ * v * l₂ * z) = z * l₂ * z := by
        have e' : ((l₁ : G) * v * z)⁻¹ * (l₁ * v * l₂ * z) = z⁻¹ * l₂ * z := by group
        rwa [h.inv_z] at e'
      rw [e]
      exact h.L_le_M (h.hzL l₂ hl₂)
  · rintro (hp | ⟨x, rfl⟩)
    · rw [Set.mem_singleton_iff] at hp
      exact ⟨1, by rw [hp]; exact one_smul _ _⟩
    · induction x using QuotientGroup.induction_on with
      | H l =>
        refine ⟨⟨(l : G) * v, h.M.mul_mem (h.L_le_M l.2) h.v_mem_M⟩, ?_⟩
        rw [eMap_mk]
        show (((l : G) * v * z : G) : G ⧸ h.M) = _
        rfl

theorem smul_ω₁_eq_iff_mem_L {g : G} (hg : g ∈ h.M) : g • h.ω₁ = h.ω₁ ↔ g ∈ L := by
  have e : (g * z)⁻¹ * z = z * g⁻¹ * z := by
    have e' : (g * z)⁻¹ * z = z⁻¹ * g⁻¹ * z := by group
    rwa [h.inv_z] at e'
  show (((g * z : G)) : G ⧸ h.M) = ((z : G) : G ⧸ h.M) ↔ g ∈ L
  rw [QuotientGroup.eq, e]
  constructor
  · intro hm
    have := h.mem_L_of_conj_z_mem (h.M.inv_mem hg) hm
    simpa using this
  · intro hgL
    exact h.L_le_M (h.hzL _ (L.inv_mem hgL))

section Counting

variable [Finite G]

omit [Finite G] in
theorem card_stabilizer : Nat.card (stabilizer ↥h.M h.ω₁) = Nat.card ↥L :=
  Nat.card_congr
    { toFun := fun m => ⟨(m.1 : G), (h.smul_ω₁_eq_iff_mem_L m.1.2).1 m.2⟩
      invFun := fun l => ⟨⟨(l : G), h.L_le_M l.2⟩,
        (h.smul_ω₁_eq_iff_mem_L (h.L_le_M l.2)).2 l.2⟩
      left_inv := fun m => by ext; rfl
      right_inv := fun l => by ext; rfl }

theorem card_orbit (hpts : Nat.card (↥L ⧸ K.subgroupOf L) = 10) :
    Nat.card (orbit ↥h.M h.ω₁) = 11 := by
  rw [Nat.card_coe_set_eq, h.orbit_eq, Set.ncard_union_eq
    (Set.disjoint_singleton_left.2 h.ω₁_not_mem_range) (Set.toFinite _) (Set.toFinite _),
    Set.ncard_singleton, Set.ncard_range_of_injective h.eMap_injective, hpts]

theorem card_M (hLcard : Nat.card ↥L = 720) (hpts : Nat.card (↥L ⧸ K.subgroupOf L) = 10) :
    Nat.card ↥h.M = 7920 := by
  have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (stabilizer ↥h.M h.ω₁)
  have e2 : Nat.card (↥h.M ⧸ stabilizer ↥h.M h.ω₁) = 11 := by
    rw [← Nat.card_congr (orbitEquivQuotientStabilizer ↥h.M h.ω₁)]
    exact h.card_orbit hpts
  rw [e2, h.card_stabilizer, hLcard] at e1
  omega

theorem card_quotient (hG : Nat.card G = 95040) (hLcard : Nat.card ↥L = 720)
    (hpts : Nat.card (↥L ⧸ K.subgroupOf L) = 10) : Nat.card (G ⧸ h.M) = 12 := by
  have e := Subgroup.card_eq_card_quotient_mul_card_subgroup h.M
  rw [hG, h.card_M hLcard hpts] at e
  omega

theorem univ_eq (hG : Nat.card G = 95040) (hLcard : Nat.card ↥L = 720)
    (hpts : Nat.card (↥L ⧸ K.subgroupOf L) = 10) :
    (Set.univ : Set (G ⧸ h.M)) = {h.ω₀} ∪ ({h.ω₁} ∪ Set.range h.eMap) := by
  symm
  refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
  have hd : Disjoint {h.ω₀} ({h.ω₁} ∪ Set.range h.eMap) := by
    rw [Set.disjoint_singleton_left]
    rintro (hp | hp)
    · exact h.ω₁_ne_ω₀ hp.symm
    · exact h.ω₀_not_mem_range hp
  rw [Set.ncard_univ, h.card_quotient hG hLcard hpts,
    Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton,
    Set.ncard_union_eq (Set.disjoint_singleton_left.2 h.ω₁_not_mem_range) (Set.toFinite _)
      (Set.toFinite _), Set.ncard_singleton, Set.ncard_range_of_injective h.eMap_injective,
    hpts]

end Counting

theorem sharpOn_L
    (hL3 : ∀ a b : Fin 3 → (↥L ⧸ K.subgroupOf L), Function.Injective a → Function.Injective b →
      ∃! g : ↥L, ∀ i, g • a i = b i) :
    SharpOn L (Set.range h.eMap) 3 := by
  intro a b ha hb hai hbi
  choose x hx using ha
  choose y hy using hb
  have hxi : Function.Injective x := fun i j hij => hai (by rw [← hx i, ← hx j, hij])
  have hyi : Function.Injective y := fun i j hij => hbi (by rw [← hy i, ← hy j, hij])
  obtain ⟨g, hg, hgu⟩ := hL3 x y hxi hyi
  refine ⟨(g : G), ⟨g.2, fun i => ?_⟩, ?_⟩
  · rw [← hx i, ← hy i, eMap_smul, hg i]
  · rintro g' ⟨hg'L, hg'⟩
    have hmem : (⟨g', hg'L⟩ : ↥L) = g := by
      refine hgu _ (fun i => h.eMap_injective ?_)
      rw [← eMap_smul, hx i, hy i]
      exact hg' i
    exact congrArg Subtype.val hmem

theorem sharpOn_M (hG : Nat.card G = 95040) (hLcard : Nat.card ↥L = 720) [Finite G]
    (hpts : Nat.card (↥L ⧸ K.subgroupOf L) = 10)
    (hL : SharpOn L (Set.range h.eMap) 3) : SharpOn h.M ({h.ω₀}ᶜ : Set (G ⧸ h.M)) 4 := by
  have huniv := h.univ_eq hG hLcard hpts
  have hrange : ({h.ω₀}ᶜ : Set (G ⧸ h.M)) \ {h.ω₁} = Set.range h.eMap := by
    ext p
    constructor
    · rintro ⟨hp0, hp1⟩
      have : p ∈ (Set.univ : Set (G ⧸ h.M)) := Set.mem_univ p
      rw [huniv] at this
      rcases this with hp | hp | hp
      · exact absurd hp hp0
      · exact absurd hp hp1
      · exact hp
    · intro hp
      refine ⟨?_, ?_⟩
      · intro e
        exact h.ω₀_not_mem_range (by rw [← Set.mem_singleton_iff.1 e]; exact hp)
      · intro e
        exact h.ω₁_not_mem_range (by rw [← Set.mem_singleton_iff.1 e]; exact hp)
  refine SharpOn.succ h.M L _ h.ω₁ 3 ?_ ?_ ?_ ?_
  · intro g hg y hy e
    apply hy
    have := (h.smul_ω₀_eq_iff g).2 hg
    rw [Set.mem_singleton_iff] at e ⊢
    calc y = g⁻¹ • (g • y) := by rw [inv_smul_smul]
      _ = g⁻¹ • h.ω₀ := by rw [e]
      _ = h.ω₀ := by
        conv_lhs => rw [← this]
        rw [inv_smul_smul]
  · intro y hy
    have : y ∈ (Set.univ : Set (G ⧸ h.M)) := Set.mem_univ y
    rw [huniv] at this
    rcases this with hp | hp | hp
    · exact absurd hp hy
    · refine ⟨1, h.M.one_mem, ?_⟩
      rw [Set.mem_singleton_iff.1 hp, one_smul]
    · have hmem : y ∈ (orbit ↥h.M h.ω₁ : Set (G ⧸ h.M)) := by
        rw [h.orbit_eq]; exact Or.inr hp
      obtain ⟨⟨m, hm⟩, hmy⟩ := hmem
      exact ⟨m, hm, hmy⟩
  · intro g
    constructor
    · intro hg
      have hgM := h.L_le_M hg
      exact ⟨hgM, (h.smul_ω₁_eq_iff_mem_L hgM).2 hg⟩
    · rintro ⟨hgM, hg1⟩
      exact (h.smul_ω₁_eq_iff_mem_L hgM).1 hg1
  · rw [hrange]; exact hL

theorem sharpOn_G (hM : SharpOn h.M ({h.ω₀}ᶜ : Set (G ⧸ h.M)) 4) :
    SharpOn (⊤ : Subgroup G) (Set.univ : Set (G ⧸ h.M)) 5 := by
  refine SharpOn.succ ⊤ h.M Set.univ h.ω₀ 4 (fun _ _ _ _ => Set.mem_univ _) ?_ ?_ ?_
  · intro y _
    induction y using QuotientGroup.induction_on with
    | H g =>
      refine ⟨g, Subgroup.mem_top g, ?_⟩
      show (((g * 1 : G)) : G ⧸ h.M) = _
      rw [mul_one]
  · intro g
    constructor
    · intro hg; exact ⟨Subgroup.mem_top g, (h.smul_ω₀_eq_iff g).2 hg⟩
    · rintro ⟨-, hg⟩; exact (h.smul_ω₀_eq_iff g).1 hg
  · have : (Set.univ : Set (G ⧸ h.M)) \ {h.ω₀} = ({h.ω₀}ᶜ : Set (G ⧸ h.M)) := by
      ext; simp
    rw [this]; exact hM

theorem mem_stabilizer_mk_iff (g y : G) :
    g ∈ stabilizer G ((y : G) : G ⧸ h.M) ↔ y⁻¹ * g * y ∈ h.M := by
  rw [mem_stabilizer_iff]
  show (((g * y : G)) : G ⧸ h.M) = ((y : G) : G ⧸ h.M) ↔ _
  rw [QuotientGroup.eq]
  have e : (g * y)⁻¹ * y = (y⁻¹ * g * y)⁻¹ := by group
  rw [e, Subgroup.inv_mem_iff]

theorem conj_vz_mem_M_iff {x : G} (hxL : x ∈ L) : z * (v * x * v) * z ∈ h.M ↔ x ∈ K := by
  constructor
  · intro hx
    have hm : v * x * v ∈ h.M := h.M.mul_mem (h.M.mul_mem h.v_mem_M (h.L_le_M hxL)) h.v_mem_M
    exact h.mem_K_of_conj_mem hxL (h.mem_L_of_conj_z_mem hm hx)
  · intro hxK
    exact h.L_le_M (h.hzL _ (h.hKL (h.hvK x hxK)))

theorem mem_L_iff_mem_M {x : G} : x ∈ L ↔ x ∈ h.M ∧ z * x * z ∈ h.M :=
  ⟨fun hx => ⟨h.L_le_M hx, h.L_le_M (h.hzL x hx)⟩, fun hx => h.mem_L_of_conj_z_mem hx.1 hx.2⟩

theorem mem_stab_four {l₀ g : G} (hl₀ : l₀ ∈ L) :
    g ∈ stabilizer G h.ω₀ ⊓ stabilizer G h.ω₁ ⊓ stabilizer G ((v * z : G) : G ⧸ h.M) ⊓
      stabilizer G ((l₀ * v * z : G) : G ⧸ h.M) ↔ g ∈ K ∧ l₀⁻¹ * g * l₀ ∈ K := by
  have c0 : g ∈ stabilizer G h.ω₀ ↔ g ∈ h.M := by
    unfold ω₀
    rw [h.mem_stabilizer_mk_iff]; simp
  have c1 : g ∈ stabilizer G h.ω₁ ↔ z * g * z ∈ h.M := by
    unfold ω₁
    rw [h.mem_stabilizer_mk_iff, h.inv_z]
  have c3 : g ∈ stabilizer G ((v * z : G) : G ⧸ h.M) ↔ z * (v * g * v) * z ∈ h.M := by
    rw [h.mem_stabilizer_mk_iff]
    have e : (v * z)⁻¹ * g * (v * z) = z * (v * g * v) * z := by
      have e' : (v * z)⁻¹ * g * (v * z) = z⁻¹ * (v⁻¹ * g * v) * z := by group
      rwa [h.inv_z, h.inv_v] at e'
    rw [e]
  have c4 : g ∈ stabilizer G ((l₀ * v * z : G) : G ⧸ h.M) ↔
      z * (v * (l₀⁻¹ * g * l₀) * v) * z ∈ h.M := by
    rw [h.mem_stabilizer_mk_iff]
    have e : (l₀ * v * z)⁻¹ * g * (l₀ * v * z) = z * (v * (l₀⁻¹ * g * l₀) * v) * z := by
      have e' : (l₀ * v * z)⁻¹ * g * (l₀ * v * z) = z⁻¹ * (v⁻¹ * (l₀⁻¹ * g * l₀) * v) * z := by
        group
      rwa [h.inv_z, h.inv_v] at e'
    rw [e]
  simp only [Subgroup.mem_inf, c0, c1, c3, c4]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, h3⟩, h4⟩
    have hgL : g ∈ L := h.mem_L_iff_mem_M.2 ⟨h0, h1⟩
    have hconj : l₀⁻¹ * g * l₀ ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl₀) hgL) hl₀
    exact ⟨(h.conj_vz_mem_M_iff hgL).1 h3, (h.conj_vz_mem_M_iff hconj).1 h4⟩
  · rintro ⟨hgK, hconjK⟩
    have hgL : g ∈ L := h.hKL hgK
    have hconj : l₀⁻¹ * g * l₀ ∈ L := h.hKL hconjK
    exact ⟨⟨⟨h.L_le_M hgL, h.L_le_M (h.hzL g hgL)⟩, (h.conj_vz_mem_M_iff hgL).2 hgK⟩,
      (h.conj_vz_mem_M_iff hconj).2 hconjK⟩

theorem faithful [IsSimpleGroup G] : FaithfulSMul G (G ⧸ h.M) := by
  have : (MulAction.toPermHom G (G ⧸ h.M)).ker.Normal := MonoidHom.normal_ker _
  refine ⟨fun {g₁ g₂} hg => ?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (MulAction.toPermHom G (G ⧸ h.M)).ker with hN | hN
  · have hmem : g₁⁻¹ * g₂ ∈ (MulAction.toPermHom G (G ⧸ h.M)).ker := by
      rw [MonoidHom.mem_ker]
      ext x
      show (g₁⁻¹ * g₂) • x = x
      rw [mul_smul, ← hg x, inv_smul_smul]
    rw [hN, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem
  · exfalso
    have hz' : z ∈ (MulAction.toPermHom G (G ⧸ h.M)).ker := by
      rw [hN]; exact Subgroup.mem_top z
    rw [MonoidHom.mem_ker] at hz'
    have e : z • h.ω₀ = h.ω₀ := by
      have := congrArg (fun σ : Equiv.Perm (G ⧸ h.M) => σ h.ω₀) hz'
      exact this
    exact h.z_not_mem_M ((h.smul_ω₀_eq_iff z).1 e)

end TailCore

theorem exists_third {X : Type*} [Finite X] (hX : 3 ≤ Nat.card X) (p q : X) :
    ∃ t, t ≠ p ∧ t ≠ q := by
  by_contra hcon
  have hcon' : ∀ t, t ≠ p → t = q := fun t hp => by_contra fun hq => hcon ⟨t, hp, hq⟩
  have hsub : (Set.univ : Set X) ⊆ {p, q} := fun t _ => by
    by_cases hp : t = p
    · simp [hp]
    · simp [hcon' t hp]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ] at h1
  have h2 : ({p, q} : Set X).ncard ≤ 2 := by
    have := Set.ncard_insert_le p ({q} : Set X)
    rw [Set.ncard_singleton] at this
    exact this
  omega

theorem exists_double_coset {G : Type*} [Group G] (L K : Subgroup G)
    (hpts : 3 ≤ Nat.card (↥L ⧸ K.subgroupOf L)) [Finite (↥L ⧸ K.subgroupOf L)]
    (hL3 : ∀ a b : Fin 3 → (↥L ⧸ K.subgroupOf L), Function.Injective a → Function.Injective b →
      ∃! g : ↥L, ∀ i, g • a i = b i)
    {r : G} (hrL : r ∈ L) (hrK : r ∉ K) {l : G} (hl : l ∈ L) (hlK : l ∉ K) :
    ∃ k₁ ∈ K, ∃ k₂ ∈ K, l = k₁ * r * k₂ := by
  set p₀ : ↥L ⧸ K.subgroupOf L := QuotientGroup.mk 1 with hp₀
  set p₁ : ↥L ⧸ K.subgroupOf L := QuotientGroup.mk ⟨r, hrL⟩ with hp₁
  set p₁' : ↥L ⧸ K.subgroupOf L := QuotientGroup.mk ⟨l, hl⟩ with hp₁'
  have h10 : p₁ ≠ p₀ := by
    intro e
    rw [hp₁, hp₀, QuotientGroup.eq, Subgroup.mem_subgroupOf] at e
    exact hrK (by simpa using e)
  have h10' : p₁' ≠ p₀ := by
    intro e
    rw [hp₁', hp₀, QuotientGroup.eq, Subgroup.mem_subgroupOf] at e
    exact hlK (by simpa using e)
  obtain ⟨t, ht0, ht1⟩ := exists_third hpts p₀ p₁
  obtain ⟨t', ht0', ht1'⟩ := exists_third hpts p₀ p₁'
  have inj3 : ∀ a b c : ↥L ⧸ K.subgroupOf L, a ≠ b → a ≠ c → b ≠ c →
      Function.Injective ![a, b, c] := by
    intro a b c hab hac hbc i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨g, hg, -⟩ := hL3 ![p₀, p₁, t] ![p₀, p₁', t']
    (inj3 _ _ _ h10.symm ht0.symm ht1.symm) (inj3 _ _ _ h10'.symm ht0'.symm ht1'.symm)
  have g0 : g • p₀ = p₀ := hg 0
  have g1 : g • p₁ = p₁' := hg 1
  have hgK : (g : G) ∈ K := by
    have : (((g * 1 : ↥L)) : ↥L ⧸ K.subgroupOf L) = QuotientGroup.mk 1 := g0
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at this
    simpa using this
  have hk : ((g : G) * r)⁻¹ * l ∈ K := by
    have : (((g * ⟨r, hrL⟩ : ↥L)) : ↥L ⧸ K.subgroupOf L) = QuotientGroup.mk ⟨l, hl⟩ := g1
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at this
    simpa using this
  exact ⟨g, hgK, ((g : G) * r)⁻¹ * l, hk, by group⟩

theorem exists_sharply_five_transitive_of_M10_amalgam
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hG : Nat.card G = 95040)
    (L K : Subgroup G) (hKL : K ≤ L) (v z r : G)
    (hLcard : Nat.card L = 720) (hpts : Nat.card (↥L ⧸ K.subgroupOf L) = 10)
    (hL3 : ∀ a b : Fin 3 → (↥L ⧸ K.subgroupOf L), Function.Injective a → Function.Injective b →
      ∃! g : ↥L, ∀ i, g • a i = b i)
    (hQ8 : ∃ l₀ ∈ L, l₀ ∉ K ∧ ∃ H : Subgroup G, (∀ g, g ∈ H ↔ g ∈ K ∧ l₀⁻¹ * g * l₀ ∈ K) ∧
      Nonempty (↥H ≃* QuaternionGroup 2))
    (hv : v * v = 1) (hvK : ∀ k ∈ K, v * k * v⁻¹ ∈ K) (hvL : ∃ l ∈ L, v * l * v⁻¹ ∉ L)
    (hr : r ∈ L ∧ r ∉ K ∧ r * r = 1 ∧ (r * v) ^ 3 = 1)
    (hz : z * z = 1) (hzL : ∀ l ∈ L, z * l * z⁻¹ ∈ L) (hzn : z ∉ L) (hvz : (v * z) ^ 3 = 1) :
    ∃ M : Subgroup G, Nat.card (G ⧸ M) = 12 ∧ FaithfulSMul G (G ⧸ M) ∧
      (∀ a b : Fin 5 → G ⧸ M, Function.Injective a → Function.Injective b →
        ∃! g : G, ∀ i, g • a i = b i) ∧
      (∃ w x y u : G ⧸ M, w ≠ x ∧ w ≠ y ∧ w ≠ u ∧ x ≠ y ∧ x ≠ u ∧ y ≠ u ∧
        Nonempty (↥(MulAction.stabilizer G w ⊓ MulAction.stabilizer G x ⊓
          MulAction.stabilizer G y ⊓ MulAction.stabilizer G u) ≃* QuaternionGroup 2)) := by
  obtain ⟨hrL, hrK, hrr, hrv3⟩ := hr
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hrvr : r * v * r = v * r * v := by
    have h1 : (r * v * r) * (v * r * v) = 1 := by
      have := hrv3
      simp only [pow_succ, pow_zero, one_mul, mul_assoc] at this ⊢
      exact this
    have h2 : (v * r * v)⁻¹ = v * r * v := by
      rw [mul_inv_rev, mul_inv_rev, hvi, inv_eq_of_mul_eq_one_right hrr]; group
    rw [← h2]
    exact eq_inv_of_mul_eq_one_left h1
  have hzvz : z * v * z = v * z * v := by
    have h1 : (z * v * z) * (v * z * v) = 1 := by
      have h3 : (v * z) * (v * z) * (v * z) = 1 := by simpa [pow_succ] using hvz
      calc (z * v * z) * (v * z * v) = v⁻¹ * ((v * z) * (v * z) * (v * z)) * v := by group
        _ = 1 := by rw [h3]; group
    have h2 : (v * z * v)⁻¹ = v * z * v := by
      rw [mul_inv_rev, mul_inv_rev, hvi, hzi]; group
    rw [← h2]
    exact eq_inv_of_mul_eq_one_left h1
  have hcore : TailCore L K v z r :=
    { hKL := hKL
      hv := hv
      hvK := fun k hk => by simpa [hvi] using hvK k hk
      hvL := by
        obtain ⟨l, hl, hn⟩ := hvL
        exact ⟨l, hl, by simpa [hvi] using hn⟩
      hrL := hrL
      hrr := hrr
      hrv := hrvr
      hdc := fun l hl => by
        by_cases hlK : l ∈ K
        · exact Or.inl hlK
        · exact Or.inr (exists_double_coset L K (by rw [hpts]; norm_num) hL3 hrL hrK hl hlK)
      hz := hz
      hzL := fun l hl => by simpa [hzi] using hzL l hl
      hzn := hzn
      hzv := hzvz }
  have hsharp := hcore.sharpOn_G (hcore.sharpOn_M hG hLcard hpts (hcore.sharpOn_L hL3))
  refine ⟨hcore.M, hcore.card_quotient hG hLcard hpts, hcore.faithful, ?_, ?_⟩
  · intro a b ha hb
    obtain ⟨g, ⟨-, hg⟩, hu⟩ := hsharp a b (fun _ => Set.mem_univ _) (fun _ => Set.mem_univ _) ha hb
    exact ⟨g, hg, fun g' hg' => hu g' ⟨Subgroup.mem_top _, hg'⟩⟩
  · obtain ⟨l₀, hl₀L, hl₀K, H, hH, ⟨φ⟩⟩ := hQ8
    have hy' : hcore.eMap (QuotientGroup.mk 1) = ((v * z : G) : G ⧸ hcore.M) := by
      rw [TailCore.eMap_mk]; simp
    have hu' : hcore.eMap (QuotientGroup.mk ⟨l₀, hl₀L⟩) = ((l₀ * v * z : G) : G ⧸ hcore.M) :=
      TailCore.eMap_mk hcore ⟨l₀, hl₀L⟩
    have hy : ((v * z : G) : G ⧸ hcore.M) ∈ Set.range hcore.eMap := ⟨_, hy'⟩
    have hu : ((l₀ * v * z : G) : G ⧸ hcore.M) ∈ Set.range hcore.eMap := ⟨_, hu'⟩
    refine ⟨hcore.ω₀, hcore.ω₁, ((v * z : G) : G ⧸ hcore.M), ((l₀ * v * z : G) : G ⧸ hcore.M),
      hcore.ω₁_ne_ω₀.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e; exact hcore.ω₀_not_mem_range (by rw [e]; exact hy)
    · intro e; exact hcore.ω₀_not_mem_range (by rw [e]; exact hu)
    · intro e; exact hcore.ω₁_not_mem_range (by rw [e]; exact hy)
    · intro e; exact hcore.ω₁_not_mem_range (by rw [e]; exact hu)
    · intro e
      have e' := hcore.eMap_injective (hy'.trans (e.trans hu'.symm))
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at e'
      exact hl₀K (by simpa using e')
    · have heq : (stabilizer G hcore.ω₀ ⊓ stabilizer G hcore.ω₁ ⊓
          stabilizer G ((v * z : G) : G ⧸ hcore.M) ⊓
          stabilizer G ((l₀ * v * z : G) : G ⧸ hcore.M)) = H := by
        ext g
        rw [hcore.mem_stab_four hl₀L, hH]
      exact ⟨(MulEquiv.subgroupCongr heq).trans φ⟩

end CFSG.Quasithin
