module

public import CFSG.Sporadic.Co1Patterson.Defs
public import CFSG.Monster.GMS.Leech.TypeUniqueFiber

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open scoped commutatorElement

structure Nondeg {n : ℕ} (bil : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2) : Prop where
  exists_eq_one : ∃ u v, bil u v = 1
  exists_eq : ∀ D : (Fin n → ZMod 2) → ZMod 2, (∀ u v, D (u + v) = D u + D v) →
    ∃ a, ∀ v, D v = bil a v

theorem vec_add_self {n : ℕ} (v : Fin n → ZMod 2) : v + v = 0 :=
  funext fun i => CharTwo.add_self_eq_zero (v i)

namespace ExtraspecialTypeSystem

variable {n : ℕ} {L : Type} [Group L] {act : L →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))}
  {qf : (Fin n → ZMod 2) → ZMod 2} {bil : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2}
  {H : Type} [Group H] (S : ExtraspecialTypeSystem n L act qf bil H)

theorem vec_one : S.vec 1 = 0 := (S.vec_eq_zero 1 (map_one S.φ)).2 (Or.inl rfl)

theorem vec_z : S.vec S.z = 0 := (S.vec_eq_zero S.z S.φ_z).2 (Or.inr rfl)

theorem vec_inv {q : H} (hq : S.φ q = 1) : S.vec q⁻¹ = S.vec q := by
  have h := S.vec_mul q q⁻¹ hq (by rw [map_inv, hq, inv_one])
  rw [mul_inv_cancel, S.vec_one] at h
  exact add_left_cancel (h.symm.trans (vec_add_self (S.vec q)).symm)

theorem commElt_eq_one_iff {p q : H} (hp : S.φ p = 1) (hq : S.φ q = 1) :
    ⁅p, q⁆ = 1 ↔ bil (S.vec p) (S.vec q) = 0 := by
  rw [commutatorElement_def]
  exact S.comm_eq_one_iff p q hp hq

theorem commElt_eq_z_iff {p q : H} (hp : S.φ p = 1) (hq : S.φ q = 1) :
    ⁅p, q⁆ = S.z ↔ bil (S.vec p) (S.vec q) = 1 := by
  rw [commutatorElement_def]
  exact S.comm_eq_z_iff p q hp hq

theorem comm_cases {p q : H} (hp : S.φ p = 1) (hq : S.φ q = 1) :
    ⁅p, q⁆ = 1 ∨ ⁅p, q⁆ = S.z := by
  rcases CFSG.Sporadic.Co1.Module.zmod2_cases (bil (S.vec p) (S.vec q)) with h | h
  · exact Or.inl ((S.commElt_eq_one_iff hp hq).2 h)
  · exact Or.inr ((S.commElt_eq_z_iff hp hq).2 h)

end ExtraspecialTypeSystem

variable {n : ℕ} {L : Type} [Group L] {act : L →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))}
  {qf : (Fin n → ZMod 2) → ZMod 2} {bil : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2}
  {H H' : Type} [Group H] [Group H'] {S : ExtraspecialTypeSystem n L act qf bil H}
  {S' : ExtraspecialTypeSystem n L act qf bil H'}

namespace Glue

@[expose] def P0 (S : ExtraspecialTypeSystem n L act qf bil H)
    (S' : ExtraspecialTypeSystem n L act qf bil H') : Subgroup (H × H') where
  carrier := {g | S.φ g.1 = S'.φ g.2}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul, map_mul] at ha hb ⊢
    rw [ha, hb]
  one_mem' := by simp
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq, Prod.fst_inv, Prod.snd_inv, map_inv] at ha ⊢
    rw [ha]

theorem mem_P0 {g : H × H'} : g ∈ P0 S S' ↔ S.φ g.1 = S'.φ g.2 := Iff.rfl

@[expose] def F (S : ExtraspecialTypeSystem n L act qf bil H)
    (S' : ExtraspecialTypeSystem n L act qf bil H') : Subgroup (H × H') where
  carrier := {g | S.φ g.1 = 1 ∧ S'.φ g.2 = 1 ∧ S.vec g.1 = S'.vec g.2}
  mul_mem' := fun {a b} ha hb => by
    obtain ⟨ha1, ha2, ha3⟩ := ha
    obtain ⟨hb1, hb2, hb3⟩ := hb
    refine ⟨?_, ?_, ?_⟩
    · simp [ha1, hb1]
    · simp [ha2, hb2]
    · simp only [Prod.fst_mul, Prod.snd_mul]
      rw [S.vec_mul _ _ ha1 hb1, S'.vec_mul _ _ ha2 hb2, ha3, hb3]
  one_mem' := ⟨by simp, by simp, by simp [S.vec_one, S'.vec_one]⟩
  inv_mem' := fun {a} ha => by
    obtain ⟨ha1, ha2, ha3⟩ := ha
    refine ⟨?_, ?_, ?_⟩
    · simp [ha1]
    · simp [ha2]
    · simp only [Prod.fst_inv, Prod.snd_inv]
      rw [S.vec_inv ha1, S'.vec_inv ha2, ha3]

theorem mem_F {g : H × H'} :
    g ∈ F S S' ↔ S.φ g.1 = 1 ∧ S'.φ g.2 = 1 ∧ S.vec g.1 = S'.vec g.2 := Iff.rfl

theorem F_le_P0 : F S S' ≤ P0 S S' := fun _ hg => hg.1.trans hg.2.1.symm

theorem conj_mem_F {g f : H × H'} (hg : g ∈ P0 S S') (hf : f ∈ F S S') :
    g * f * g⁻¹ ∈ F S S' := by
  obtain ⟨x, y⟩ := g
  obtain ⟨a, b⟩ := f
  obtain ⟨h1, h2, h3⟩ := hf
  have hxy : S.φ x = S'.φ y := hg
  simp only at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · simp [h1]
  · simp [h2]
  · simp only [Prod.mk_mul_mk, Prod.inv_mk]
    rw [S.vec_conj x a h1, S'.vec_conj y b h2, ← hxy, h3]

theorem z1_mem_F : (S.z, (1 : H')) ∈ F S S' :=
  ⟨S.φ_z, map_one S'.φ, by simp [S.vec_z, S'.vec_one]⟩

theorem one_z_mem_F : ((1 : H), S'.z) ∈ F S S' :=
  ⟨map_one S.φ, S'.φ_z, by simp [S.vec_one, S'.vec_z]⟩

theorem zz_mem_F : (S.z, S'.z) ∈ F S S' :=
  ⟨S.φ_z, S'.φ_z, by simp [S.vec_z, S'.vec_z]⟩

theorem z1_comm (h : H × H') : (S.z, (1 : H')) * h = h * (S.z, 1) := by
  obtain ⟨a, b⟩ := h
  simp [S.z_comm a]

theorem one_z_comm (h : H × H') : ((1 : H), S'.z) * h = h * (1, S'.z) := by
  obtain ⟨a, b⟩ := h
  simp [S'.z_comm b]

theorem conj_central {G : Type*} [Group G] {c : G} (hc : ∀ h, c * h = h * c) (g : G) :
    g * c * g⁻¹ = c := by
  rw [← hc g, mul_assoc, mul_inv_cancel, mul_one]

theorem F_sq {f : H × H'} (hf : f ∈ F S S') : f * f = 1 ∨ f * f = (S.z, S'.z) := by
  obtain ⟨a, b⟩ := f
  obtain ⟨h1, h2, h3⟩ := hf
  simp only at h1 h2 h3
  rcases CFSG.Sporadic.Co1.Module.zmod2_cases (qf (S.vec a)) with h | h
  · left
    have hb : qf (S'.vec b) = 0 := h3 ▸ h
    rw [Prod.mk_mul_mk, (S.mul_self_eq_one_iff a h1).2 h, (S'.mul_self_eq_one_iff b h2).2 hb]
    rfl
  · right
    have hb : qf (S'.vec b) = 1 := h3 ▸ h
    rw [Prod.mk_mul_mk, (S.mul_self_eq_z_iff a h1).2 h, (S'.mul_self_eq_z_iff b h2).2 hb]

theorem F_comm {f f' : H × H'} (hf : f ∈ F S S') (hf' : f' ∈ F S S') :
    ⁅f, f'⁆ = 1 ∨ ⁅f, f'⁆ = (S.z, S'.z) := by
  obtain ⟨a, b⟩ := f
  obtain ⟨a', b'⟩ := f'
  obtain ⟨h1, h2, h3⟩ := hf
  obtain ⟨h1', h2', h3'⟩ := hf'
  simp only at h1 h2 h3 h1' h2' h3'
  have hc : ⁅((a, b) : H × H'), (a', b')⁆ = (⁅a, a'⁆, ⁅b, b'⁆) := by
    simp [commutatorElement_def]
  rw [hc]
  rcases CFSG.Sporadic.Co1.Module.zmod2_cases (bil (S.vec a) (S.vec a')) with h | h
  · left
    have hb : bil (S'.vec b) (S'.vec b') = 0 := by
      rw [← h3, ← h3']
      exact h
    rw [(S.commElt_eq_one_iff h1 h1').2 h, (S'.commElt_eq_one_iff h2 h2').2 hb]
    rfl
  · right
    have hb : bil (S'.vec b) (S'.vec b') = 1 := by
      rw [← h3, ← h3']
      exact h
    rw [(S.commElt_eq_z_iff h1 h1').2 h, (S'.commElt_eq_z_iff h2 h2').2 hb]

end Glue

open Glue in
structure Glue (S : ExtraspecialTypeSystem n L act qf bil H)
    (S' : ExtraspecialTypeSystem n L act qf bil H') where
  m : H × H' → ZMod 2
  m_mul : ∀ a ∈ F S S', ∀ b ∈ F S S', m (a * b) = m a + m b
  m_z1 : m (S.z, 1) = 1
  m_zz : m (S.z, S'.z) = 0

open Glue in
theorem exists_glue (hb : ∃ u v, bil u v = 1) (S : ExtraspecialTypeSystem n L act qf bil H)
    (S' : ExtraspecialTypeSystem n L act qf bil H') : Nonempty (Glue S S') := by
  classical
  let nn : F S S' := ⟨(S.z, S'.z), zz_mem_F⟩
  let x : F S S' := ⟨(S.z, 1), z1_mem_F⟩
  have hnc : ∃ a b : F S S', ⁅a, b⁆ = nn := by
    obtain ⟨u, v, hv⟩ := hb
    obtain ⟨a, ha, hau⟩ := S.vec_surj u
    obtain ⟨a', ha', hav⟩ := S.vec_surj v
    obtain ⟨b, hb, hbu⟩ := S'.vec_surj u
    obtain ⟨b', hb', hbv⟩ := S'.vec_surj v
    refine ⟨⟨(a, b), ha, hb, hau.trans hbu.symm⟩, ⟨(a', b'), ha', hb', hav.trans hbv.symm⟩, ?_⟩
    apply Subtype.ext
    show ⁅((a, b) : H × H'), (a', b')⁆ = (S.z, S'.z)
    have hc : ⁅((a, b) : H × H'), (a', b')⁆ = (⁅a, a'⁆, ⁅b, b'⁆) := by
      simp [commutatorElement_def]
    rw [hc, (S.commElt_eq_z_iff ha ha').2 (by rw [hau, hav]; exact hv),
      (S'.commElt_eq_z_iff hb hb').2 (by rw [hbu, hbv]; exact hv)]
  obtain ⟨m₀, hm₀, hx, hn⟩ := CFSG.Monster.GMS.exists_zmod_two_hom nn x
    (Subtype.ext (Prod.ext S.z_mul_self S'.z_mul_self))
    (fun a => (F_sq a.2).imp Subtype.ext Subtype.ext)
    (fun a b => (F_comm a.2 b.2).imp Subtype.ext Subtype.ext) hnc
    (fun h => S.z_ne_one (congrArg (fun a : F S S' => a.1.1) h))
    (fun h => S'.z_ne_one (congrArg (fun a : F S S' => a.1.2) h).symm)
  refine ⟨⟨fun g => if h : g ∈ F S S' then m₀ ⟨g, h⟩ else 0, ?_, ?_, ?_⟩⟩
  · intro a ha b hb
    simp only [ha, hb, mul_mem ha hb, ↓reduceDIte]
    exact hm₀ ⟨a, ha⟩ ⟨b, hb⟩
  · simpa [z1_mem_F] using hx
  · simpa [zz_mem_F] using hn

namespace Glue

variable (G : Glue S S')

theorem m_one : G.m 1 = 0 := by
  have h := G.m_mul 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at h
  linear_combination (-1 : ZMod 2) * h

theorem m_inv {f : H × H'} (hf : f ∈ F S S') : G.m f⁻¹ = G.m f := by
  have h := G.m_mul f hf f⁻¹ (inv_mem hf)
  rw [mul_inv_cancel, G.m_one] at h
  rw [eq_neg_of_add_eq_zero_right h.symm, CharTwo.neg_eq]

theorem m_one_z : G.m (1, S'.z) = 1 := by
  have h := G.m_mul _ z1_mem_F _ zz_mem_F
  rw [G.m_z1, G.m_zz, Prod.mk_mul_mk, S.z_mul_self, one_mul, add_zero] at h
  exact h

@[expose] def Δ : Subgroup (H × H') where
  carrier := {f | f ∈ F S S' ∧ G.m f = 0}
  mul_mem' := fun {a b} ha hb =>
    ⟨mul_mem ha.1 hb.1, by rw [G.m_mul a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
  one_mem' := ⟨one_mem _, G.m_one⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [G.m_inv ha.1, ha.2]⟩

theorem mem_Δ {f : H × H'} : f ∈ G.Δ ↔ f ∈ F S S' ∧ G.m f = 0 := Iff.rfl

theorem Δ_le_F : G.Δ ≤ F S S' := fun _ hf => hf.1

theorem zz_mem_Δ : (S.z, S'.z) ∈ G.Δ := ⟨zz_mem_F, G.m_zz⟩

theorem z1_not_mem_Δ : (S.z, (1 : H')) ∉ G.Δ := fun h => by
  have := h.2
  rw [G.m_z1] at this
  exact one_ne_zero this

theorem one_z_not_mem_Δ : ((1 : H), S'.z) ∉ G.Δ := fun h => by
  have := h.2
  rw [G.m_one_z] at this
  exact one_ne_zero this

theorem eq_one_of_one_mem_Δ {c : H'} (h : ((1 : H), c) ∈ G.Δ) : c = 1 := by
  obtain ⟨⟨h1, h2, h3⟩, hm⟩ := h
  simp only at h1 h2 h3
  have h0 : S'.vec c = 0 := by rw [← h3, S.vec_one]
  rcases (S'.vec_eq_zero c h2).1 h0 with h | h
  · exact h
  · exfalso
    apply G.one_z_not_mem_Δ
    rw [h] at hm
    exact ⟨one_z_mem_F, hm⟩

theorem eq_one_of_mem_Δ_one {c : H} (h : (c, (1 : H')) ∈ G.Δ) : c = 1 := by
  obtain ⟨⟨h1, h2, h3⟩, hm⟩ := h
  simp only at h1 h2 h3
  have h0 : S.vec c = 0 := by rw [h3, S'.vec_one]
  rcases (S.vec_eq_zero c h1).1 h0 with h | h
  · exact h
  · exfalso
    apply G.z1_not_mem_Δ
    rw [h] at hm
    exact ⟨z1_mem_F, hm⟩

theorem mem_Δ_or_z1_mul {f : H × H'} (hf : f ∈ F S S') :
    f ∈ G.Δ ∨ (S.z, (1 : H')) * f ∈ G.Δ := by
  rcases CFSG.Sporadic.Co1.Module.zmod2_cases (G.m f) with h | h
  · exact Or.inl ⟨hf, h⟩
  · refine Or.inr ⟨mul_mem z1_mem_F hf, ?_⟩
    rw [G.m_mul _ z1_mem_F f hf, G.m_z1, h]
    decide

theorem mem_Δ_or_one_z_mul {f : H × H'} (hf : f ∈ F S S') :
    f ∈ G.Δ ∨ ((1 : H), S'.z) * f ∈ G.Δ := by
  rcases CFSG.Sporadic.Co1.Module.zmod2_cases (G.m f) with h | h
  · exact Or.inl ⟨hf, h⟩
  · refine Or.inr ⟨mul_mem one_z_mem_F hf, ?_⟩
    rw [G.m_mul _ one_z_mem_F f hf, G.m_one_z, h]
    decide

theorem exists_mem_Δ_snd {q : H'} (hq : S'.φ q = 1) : ∃ a : H, (a, q) ∈ G.Δ := by
  obtain ⟨a, ha, hav⟩ := S.vec_surj (S'.vec q)
  rcases G.mem_Δ_or_z1_mul (f := (a, q)) ⟨ha, hq, hav⟩ with h | h
  · exact ⟨a, h⟩
  · exact ⟨S.z * a, by simpa using h⟩

theorem exists_mem_Δ_fst {a : H} (ha : S.φ a = 1) : ∃ c : H', (a, c) ∈ G.Δ := by
  obtain ⟨c, hc, hcv⟩ := S'.vec_surj (S.vec a)
  rcases G.mem_Δ_or_one_z_mul (f := (a, c)) ⟨ha, hc, hcv.symm⟩ with h | h
  · exact ⟨c, h⟩
  · exact ⟨S'.z * c, by simpa using h⟩

end Glue

end CFSG.Sporadic.Co1Patterson
