module

public import CFSG.Quasithin.EmptyFaithful.S152NPairA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace S152Fin

theorem exists_mul_of_mem_sup_of_normalizes {K M : Subgroup G}
    (h : ∀ k ∈ K, ∀ m ∈ M, k * m * k⁻¹ ∈ M) {x : G} (hx : x ∈ K ⊔ M) :
    ∃ k ∈ K, ∃ m ∈ M, x = k * m := by
  let S : Subgroup G :=
    { carrier := {x | ∃ k ∈ K, ∃ m ∈ M, x = k * m}
      mul_mem' := by
        rintro _ _ ⟨k, hk, m, hm, rfl⟩ ⟨k', hk', m', hm', rfl⟩
        refine ⟨k * k', K.mul_mem hk hk', (k'⁻¹ * m * k') * m', ?_, ?_⟩
        · exact M.mul_mem (by simpa using h k'⁻¹ (K.inv_mem hk') m hm) hm'
        · group
      one_mem' := ⟨1, K.one_mem, 1, M.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨k, hk, m, hm, rfl⟩
        refine ⟨k⁻¹, K.inv_mem hk, k * m⁻¹ * k⁻¹, h k hk _ (M.inv_mem hm), ?_⟩
        group }
  have hKS : K ≤ S := fun k hk => ⟨k, hk, 1, M.one_mem, by simp⟩
  have hMS : M ≤ S := fun m hm => ⟨1, K.one_mem, m, hm, by simp⟩
  exact (sup_le hKS hMS : K ⊔ M ≤ S) hx

variable {H U L N B F₁ F₂ X₁ X₂ : Subgroup G}

namespace PairStep

variable (P : PairStep H U L N B F₁ F₂ X₁ X₂)

include P in
theorem B_le_normalizer_L : B ≤ Subgroup.normalizer (L : Set G) :=
  le_normalizer_of_conj fun f hf l hl => P.H_norm_L f (P.B_le hf) l hl

include P in
theorem N_abelian : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := fun _ ha _ hb =>
  F7.isElemAbelian_comm P.elemAbelian (P.step.1.1 ha) (P.step.1.1 hb)

include P in
theorem L_le_N : L ≤ N := P.step.2.2.1.le

include P in
theorem mem_C₁ {f : G} : f ∈ cSecIn B L X₁ ↔ f ∈ B ∧ ∀ x ∈ X₁, f * x * f⁻¹ * x⁻¹ ∈ L :=
  ⟨fun h => mem_cSecIn P.B_le_normalizer_L h, fun h => Subgroup.subset_closure h⟩

include P in
theorem mem_C₂ {f : G} : f ∈ cSecIn B L X₂ ↔ f ∈ B ∧ ∀ x ∈ X₂, f * x * f⁻¹ * x⁻¹ ∈ L :=
  ⟨fun h => mem_cSecIn P.B_le_normalizer_L h, fun h => Subgroup.subset_closure h⟩

include P in
theorem Q_le_C₁ : pCoreOf 2 H ≤ cSecIn B L X₁ := by
  intro q hq
  have hq' : q ∈ cSecIn H L N := P.hK ▸ hq
  obtain ⟨-, hqN⟩ := mem_cSecIn (le_normalizer_of_conj P.H_norm_L) hq'
  exact P.mem_C₁.mpr ⟨P.Q_le_B hq, fun x hx => hqN x (P.X₁_le hx)⟩

include P in
theorem Q_le_C₂ : pCoreOf 2 H ≤ cSecIn B L X₂ := by
  intro q hq
  have hq' : q ∈ cSecIn H L N := P.hK ▸ hq
  obtain ⟨-, hqN⟩ := mem_cSecIn (le_normalizer_of_conj P.H_norm_L) hq'
  exact P.mem_C₂.mpr ⟨P.Q_le_B hq, fun x hx => hqN x (P.X₂_le hx)⟩

include P in
theorem F₁_le_C₂ : F₁ ≤ cSecIn B L X₂ := fun f hf =>
  P.mem_C₂.mpr ⟨P.FFB ▸ (le_sup_left : F₁ ≤ F₁ ⊔ F₂) hf, P.F₁_triv f hf⟩

include P in
theorem F₂_le_C₁ : F₂ ≤ cSecIn B L X₁ := fun f hf =>
  P.mem_C₁.mpr ⟨P.FFB ▸ (le_sup_right : F₂ ≤ F₁ ⊔ F₂) hf, P.F₂_triv f hf⟩

include P in
theorem C₁_normalized {b h : G} (hb : b ∈ B) (hh : h ∈ cSecIn B L X₁) :
    b * h * b⁻¹ ∈ cSecIn B L X₁ := by
  obtain ⟨hhB, hh1⟩ := P.mem_C₁.mp hh
  refine P.mem_C₁.mpr ⟨?_, fun x hx => ?_⟩
  · exact B.mul_mem (B.mul_mem hb hhB) (B.inv_mem hb)
  · have hx' : b⁻¹ * x * b ∈ X₁ := by
      simpa using P.B_norm₁ b⁻¹ (B.inv_mem hb) x hx
    have h1 := hh1 _ hx'
    have e : b * h * b⁻¹ * x * (b * h * b⁻¹)⁻¹ * x⁻¹ =
        b * (h * (b⁻¹ * x * b) * h⁻¹ * (b⁻¹ * x * b)⁻¹) * b⁻¹ := by group
    rw [e]
    exact P.H_norm_L b (P.B_le hb) _ h1

include P in
theorem C₂_normalized {b h : G} (hb : b ∈ B) (hh : h ∈ cSecIn B L X₂) :
    b * h * b⁻¹ ∈ cSecIn B L X₂ := by
  obtain ⟨hhB, hh1⟩ := P.mem_C₂.mp hh
  refine P.mem_C₂.mpr ⟨?_, fun x hx => ?_⟩
  · exact B.mul_mem (B.mul_mem hb hhB) (B.inv_mem hb)
  · have hx' : b⁻¹ * x * b ∈ X₂ := by
      simpa using P.B_norm₂ b⁻¹ (B.inv_mem hb) x hx
    have h1 := hh1 _ hx'
    have e : b * h * b⁻¹ * x * (b * h * b⁻¹)⁻¹ * x⁻¹ =
        b * (h * (b⁻¹ * x * b) * h⁻¹ * (b⁻¹ * x * b)⁻¹) * b⁻¹ := by group
    rw [e]
    exact P.H_norm_L b (P.B_le hb) _ h1

include P in
theorem C_inf_le : cSecIn B L X₁ ⊓ cSecIn B L X₂ ≤ pCoreOf 2 H := by
  rintro h ⟨h1, h2⟩
  obtain ⟨hhB, hh1⟩ := P.mem_C₁.mp h1
  obtain ⟨-, hh2⟩ := P.mem_C₂.mp h2
  rw [← P.hK]
  apply Subgroup.subset_closure
  refine ⟨P.B_le hhB, fun n hn => ?_⟩
  have hN : N ≤ fixOne h L N P.N_abelian P.L_le_N := by
    calc N = X₁ ⊔ X₂ := P.sup_eq.symm
      _ ≤ fixOne h L N P.N_abelian P.L_le_N :=
        sup_le (fun n hn => ⟨P.X₁_le hn, hh1 n hn⟩) (fun n hn => ⟨P.X₂_le hn, hh2 n hn⟩)
  exact (hN hn).2

include P in
theorem comm_F {f₁ f₂ : G} (h₁ : f₁ ∈ F₁) (h₂ : f₂ ∈ F₂) :
    f₁ * f₂ * f₁⁻¹ * f₂⁻¹ ∈ pCoreOf 2 H := by
  have hB₁ : f₁ ∈ B := P.FFB ▸ (le_sup_left : F₁ ≤ F₁ ⊔ F₂) h₁
  have hB₂ : f₂ ∈ B := P.FFB ▸ (le_sup_right : F₂ ≤ F₁ ⊔ F₂) h₂
  apply P.C_inf_le
  constructor
  · exact (cSecIn B L X₁).mul_mem (P.C₁_normalized hB₁ (P.F₂_le_C₁ h₂))
      ((cSecIn B L X₁).inv_mem (P.F₂_le_C₁ h₂))
  · have e : f₁ * f₂ * f₁⁻¹ * f₂⁻¹ = f₁ * (f₂ * f₁⁻¹ * f₂⁻¹) := by group
    rw [e]
    have : f₂ * f₁⁻¹ * f₂⁻¹ ∈ cSecIn B L X₂ :=
      P.C₂_normalized hB₂ ((cSecIn B L X₂).inv_mem (P.F₁_le_C₂ h₁))
    exact (cSecIn B L X₂).mul_mem (P.F₁_le_C₂ h₁) this

include P in
theorem F₁_conj_F₂Q {f g : G} (hf : f ∈ F₁) (hg : g ∈ F₂ ⊔ pCoreOf 2 H) :
    f * g * f⁻¹ ∈ F₂ ⊔ pCoreOf 2 H := by
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · have hc := P.comm_F hf hx
      have e : f * x * f⁻¹ = (f * x * f⁻¹ * x⁻¹) * x := by group
      rw [e]
      exact (F₂ ⊔ pCoreOf 2 H).mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hx)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 H (P.F₁_le hf)) x).mp hx)
  | one => simp
  | mul a b _ _ ha hb =>
    have e : f * (a * b) * f⁻¹ = (f * a * f⁻¹) * (f * b * f⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have e : f * a⁻¹ * f⁻¹ = (f * a * f⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ha

include P in
theorem decomposition {b : G} (hb : b ∈ B) :
    ∃ f₁ ∈ F₁, ∃ f₂ ∈ F₂, ∃ q ∈ pCoreOf 2 H, b = f₁ * f₂ * q := by
  have hb' : b ∈ F₁ ⊔ (F₂ ⊔ pCoreOf 2 H) := by
    rw [← P.FFB] at hb
    exact (sup_le_sup_left le_sup_left F₁) hb
  obtain ⟨f₁, hf₁, g, hg, rfl⟩ :=
    exists_mul_of_mem_sup_of_normalizes (fun k hk m hm => P.F₁_conj_F₂Q hk hm) hb'
  obtain ⟨f₂, hf₂, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_normalizes
    (fun k hk m hm => (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 H (P.F₂_le hk)) m).mp hm) hg
  exact ⟨f₁, hf₁, f₂, hf₂, q, hq, by group⟩

include P in
theorem C₂_eq : cSecIn B L X₂ = F₁ ⊔ pCoreOf 2 H := by
  apply le_antisymm
  · intro b hb
    obtain ⟨hbB, hb2⟩ := P.mem_C₂.mp hb
    obtain ⟨f₁, hf₁, f₂, hf₂, q, hq, rfl⟩ := P.decomposition hbB
    have hf₂C : f₂ ∈ cSecIn B L X₂ := by
      have hf₁C := P.F₁_le_C₂ hf₁
      have hqC := P.Q_le_C₂ hq
      have e : f₂ = f₁⁻¹ * (f₁ * f₂ * q) * q⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hf₁C) hb)
        (Subgroup.inv_mem _ hqC)
    have hf₂Q : f₂ ∈ pCoreOf 2 H := P.C_inf_le ⟨P.F₂_le_C₁ hf₂, hf₂C⟩
    have e : f₁ * f₂ * q = f₁ * (f₂ * q) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hf₁)
      (Subgroup.mem_sup_right ((pCoreOf 2 H).mul_mem hf₂Q hq))
  · exact sup_le P.F₁_le_C₂ P.Q_le_C₂

include P in
theorem C₁_eq : cSecIn B L X₁ = F₂ ⊔ pCoreOf 2 H := by
  apply le_antisymm
  · intro b hb
    obtain ⟨hbB, hb1⟩ := P.mem_C₁.mp hb
    obtain ⟨f₁, hf₁, f₂, hf₂, q, hq, rfl⟩ := P.decomposition hbB
    have hf₁C : f₁ ∈ cSecIn B L X₁ := by
      have hf₂C := P.F₂_le_C₁ hf₂
      have hqC := P.Q_le_C₁ hq
      have e : f₁ = (f₁ * f₂ * q) * q⁻¹ * f₂⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb (Subgroup.inv_mem _ hqC))
        (Subgroup.inv_mem _ hf₂C)
    have hf₁Q : f₁ ∈ pCoreOf 2 H := P.C_inf_le ⟨hf₁C, P.F₁_le_C₂ hf₁⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hf₁Q) (Subgroup.mem_sup_left hf₂))
      (Subgroup.mem_sup_right hq)
  · exact sup_le P.F₂_le_C₁ P.Q_le_C₁

include P in
theorem comm_H {a b : G} (ha : a ∈ F₁ ⊔ pCoreOf 2 H) (hb : b ∈ F₂ ⊔ pCoreOf 2 H) :
    a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 H := by
  have haC : a ∈ cSecIn B L X₂ := P.C₂_eq ▸ ha
  have hbC : b ∈ cSecIn B L X₁ := P.C₁_eq ▸ hb
  have haB : a ∈ B := (P.mem_C₂.mp haC).1
  have hbB : b ∈ B := (P.mem_C₁.mp hbC).1
  apply P.C_inf_le
  constructor
  · have e : a * b * a⁻¹ * b⁻¹ = (a * b * a⁻¹) * b⁻¹ := rfl
    rw [e]
    exact Subgroup.mul_mem _ (P.C₁_normalized haB hbC) (Subgroup.inv_mem _ hbC)
  · have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ haC (P.C₂_normalized hbB (Subgroup.inv_mem _ haC))

include P in
theorem inf_H : (F₁ ⊔ pCoreOf 2 H) ⊓ (F₂ ⊔ pCoreOf 2 H) = pCoreOf 2 H := by
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    exact P.C_inf_le ⟨P.C₁_eq ▸ hx2, P.C₂_eq ▸ hx1⟩
  · exact le_inf le_sup_right le_sup_right

end PairStep

end S152Fin

end CFSG.Quasithin
