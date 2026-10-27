module

public import CFSG.Monster.GMS.Leech.TypeUniqueSystem

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

theorem exists_zmod_two_hom {A : Type*} [Group A] (n x : A) (hnn : n * n = 1)
    (hsq : ∀ a : A, a * a = 1 ∨ a * a = n) (hcomm : ∀ a b : A, ⁅a, b⁆ = 1 ∨ ⁅a, b⁆ = n)
    (hn : ∃ a b : A, ⁅a, b⁆ = n) (hx1 : x ≠ 1) (hxn : x ≠ n) :
    ∃ m : A → ZMod 2, (∀ a b, m (a * b) = m a + m b) ∧ m x = 1 ∧ m n = 0 := by
  classical
  let N : Subgroup A :=
    { carrier := {a | a = 1 ∨ a = n}
      mul_mem' := fun {a b} ha hb => by
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [hnn]
      one_mem' := Or.inl rfl
      inv_mem' := fun {a} ha => by
        rcases ha with rfl | rfl
        · simp
        · exact Or.inr (inv_eq_of_mul_eq_one_right hnn) }
  have hcle : commutator A ≤ N := by
    rw [commutator_def]
    exact Subgroup.commutator_le.2 fun a _ b _ => hcomm a b
  have hnmem : n ∈ commutator A := by
    obtain ⟨a, b, h⟩ := hn
    rw [← h]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  have hof : ∀ a ∈ commutator A, Abelianization.of a = 1 := fun a ha => by
    rw [← Abelianization.ker_of] at ha
    exact MonoidHom.mem_ker.1 ha
  have h2 : ∀ v : Additive (Abelianization A), (2 : ℕ) • v = 0 := by
    intro v
    obtain ⟨a, rfl⟩ : ∃ a : A, Additive.ofMul (Abelianization.of a) = v := by
      obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective v.toMul
      exact ⟨q, by
        change Additive.ofMul (QuotientGroup.mk q : Abelianization A) = v
        rw [hq]
        rfl⟩
    rw [← ofMul_pow, ← map_pow, pow_two]
    have : a * a ∈ commutator A := by
      rcases hsq a with h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact hnmem
    rw [hof _ this]
    rfl
  let _inst : Module (ZMod 2) (Additive (Abelianization A)) := AddCommGroup.zmodModule h2
  have hxb : Additive.ofMul (Abelianization.of x) ≠ 0 := by
    intro h
    have h' : Abelianization.of x = 1 := Additive.ofMul.injective h
    have : x ∈ commutator A := by
      rw [← Abelianization.ker_of]
      exact h'
    rcases hcle this with h1 | h1
    · exact hx1 h1
    · exact hxn h1
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hxb
  refine ⟨fun a => f (Additive.ofMul (Abelianization.of a)), fun a b => ?_, hf, ?_⟩
  · simp only [map_mul, ofMul_mul, map_add]
  · simp only [hof n hnmem]
    rw [ofMul_one]
    exact map_zero f

namespace TypeUnique

variable {H H' : Type} [Group H] [Group H'] {S : LeechTypeSystem H} {S' : LeechTypeSystem H'}

def P0 (S : LeechTypeSystem H) (S' : LeechTypeSystem H') : Subgroup (H × H') where
  carrier := {g | S.φ g.1 = S'.φ g.2}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul, map_mul] at ha hb ⊢
    rw [ha, hb]
  one_mem' := by simp
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq, Prod.fst_inv, Prod.snd_inv, map_inv] at ha ⊢
    rw [ha]

theorem mem_P0 {g : H × H'} : g ∈ P0 S S' ↔ S.φ g.1 = S'.φ g.2 := Iff.rfl

def F (S : LeechTypeSystem H) (S' : LeechTypeSystem H') : Subgroup (H × H') where
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

theorem conj_central {c : H × H'} (hc : ∀ h, c * h = h * c) (g : H × H') : g * c * g⁻¹ = c := by
  rw [← hc g, mul_assoc, mul_inv_cancel, mul_one]

theorem F_sq {f : H × H'} (hf : f ∈ F S S') : f * f = 1 ∨ f * f = (S.z, S'.z) := by
  obtain ⟨a, b⟩ := f
  obtain ⟨h1, h2, h3⟩ := hf
  simp only at h1 h2 h3
  rcases CFSG.Sporadic.Co1.Module.zmod2_cases (CFSG.Sporadic.Co1.Module.q₀ (S.vec a)) with h | h
  · left
    have hb : CFSG.Sporadic.Co1.Module.q₀ (S'.vec b) = 0 := h3 ▸ h
    rw [Prod.mk_mul_mk, (S.mul_self_eq_one_iff a h1).2 h, (S'.mul_self_eq_one_iff b h2).2 hb]
    rfl
  · right
    have hb : CFSG.Sporadic.Co1.Module.q₀ (S'.vec b) = 1 := h3 ▸ h
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
  rcases CFSG.Sporadic.Co1.Module.zmod2_cases
      (CFSG.Sporadic.Co1.Module.bil₀ (S.vec a) (S.vec a')) with h | h
  · left
    have hb : CFSG.Sporadic.Co1.Module.bil₀ (S'.vec b) (S'.vec b') = 0 := by
      rw [← h3, ← h3']
      exact h
    rw [(S.comm_eq_one_iff a a' h1 h1').2 h, (S'.comm_eq_one_iff b b' h2 h2').2 hb]
    rfl
  · right
    have hb : CFSG.Sporadic.Co1.Module.bil₀ (S'.vec b) (S'.vec b') = 1 := by
      rw [← h3, ← h3']
      exact h
    rw [(S.comm_eq_z_iff a a' h1 h1').2 h, (S'.comm_eq_z_iff b b' h2 h2').2 hb]

structure Glue (S : LeechTypeSystem H) (S' : LeechTypeSystem H') where
  m : H × H' → ZMod 2
  m_mul : ∀ a ∈ F S S', ∀ b ∈ F S S', m (a * b) = m a + m b
  m_z1 : m (S.z, 1) = 1
  m_zz : m (S.z, S'.z) = 0

theorem exists_glue
    (S : LeechTypeSystem H) (S' : LeechTypeSystem H') : Nonempty (Glue S S') := by
  classical
  let n : F S S' := ⟨(S.z, S'.z), zz_mem_F⟩
  let x : F S S' := ⟨(S.z, 1), z1_mem_F⟩
  have hnc : ∃ a b : F S S', ⁅a, b⁆ = n := by
    let u : Fin 24 → ZMod 2 := Pi.single 0 1
    have hu : u ≠ 0 := by
      intro h
      have := congrFun h 0
      simp [u] at this
    obtain ⟨v, hv⟩ := Leech.exists_bil₀_eq_one hu
    obtain ⟨a, ha, hau⟩ := S.vec_surj u
    obtain ⟨a', ha', hav⟩ := S.vec_surj v
    obtain ⟨b, hb, hbu⟩ := S'.vec_surj u
    obtain ⟨b', hb', hbv⟩ := S'.vec_surj v
    refine ⟨⟨(a, b), ha, hb, hau.trans hbu.symm⟩, ⟨(a', b'), ha', hb', hav.trans hbv.symm⟩, ?_⟩
    apply Subtype.ext
    show ⁅((a, b) : H × H'), (a', b')⁆ = (S.z, S'.z)
    have hc : ⁅((a, b) : H × H'), (a', b')⁆ = (⁅a, a'⁆, ⁅b, b'⁆) := by
      simp [commutatorElement_def]
    rw [hc, (S.comm_eq_z_iff a a' ha ha').2 (by rw [hau, hav]; exact hv),
      (S'.comm_eq_z_iff b b' hb hb').2 (by rw [hbu, hbv]; exact hv)]
  obtain ⟨m₀, hm₀, hx, hn⟩ := exists_zmod_two_hom n x
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

def Δ : Subgroup (H × H') where
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

theorem exists_translation (d : H × H' → ZMod 2)
    (hd : ∀ f₁ ∈ F S S', ∀ f₂ ∈ F S S', d (f₁ * f₂) = d f₁ + d f₂)
    (h1 : d (S.z, 1) = 0) (h2 : d (1, S'.z) = 0) :
    ∃ p : H', S'.φ p = 1 ∧
      ∀ f ∈ F S S', d f = CFSG.Sporadic.Co1.Module.bil₀ (S'.vec p) (S.vec f.1) := by
  classical
  have hd1 : d 1 = 0 := by
    have h := hd 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h
    linear_combination (-1 : ZMod 2) * h
  have hex : ∀ v, ∃ f ∈ F S S', S.vec f.1 = v := by
    intro v
    obtain ⟨a, ha, hav⟩ := S.vec_surj v
    obtain ⟨b, hb, hbv⟩ := S'.vec_surj v
    exact ⟨(a, b), ⟨ha, hb, hav.trans hbv.symm⟩, hav⟩
  have hker : ∀ f ∈ F S S', S.vec f.1 = 0 → d f = 0 := by
    intro f hf h0
    obtain ⟨a, b⟩ := f
    obtain ⟨hf1, hf2, hf3⟩ := hf
    simp only at hf1 hf2 hf3 h0
    have hb0 : S'.vec b = 0 := hf3 ▸ h0
    rcases (S.vec_eq_zero a hf1).1 h0 with rfl | rfl <;>
      rcases (S'.vec_eq_zero b hf2).1 hb0 with rfl | rfl
    · exact hd1
    · exact h2
    · exact h1
    · have := hd _ z1_mem_F _ one_z_mem_F
      rw [h1, h2, Prod.mk_mul_mk, mul_one, one_mul] at this
      simpa using this
  have hdep : ∀ f₁ ∈ F S S', ∀ f₂ ∈ F S S', S.vec f₁.1 = S.vec f₂.1 → d f₁ = d f₂ := by
    intro f₁ h₁ f₂ h₂ hv
    have hm : f₁⁻¹ * f₂ ∈ F S S' := mul_mem (inv_mem h₁) h₂
    have h0 : S.vec (f₁⁻¹ * f₂).1 = 0 := by
      have := S.vec_mul f₁.1⁻¹ f₂.1 (by simpa using (inv_mem h₁).1) h₂.1
      simp only [Prod.fst_mul, Prod.fst_inv]
      rw [this, S.vec_inv h₁.1, hv]
      exact CFSG.Sporadic.Co1.Module.vec_add_self _
    have := hd f₁ h₁ _ hm
    rw [mul_inv_cancel_left, hker _ hm h0, add_zero] at this
    exact this.symm
  let D : (Fin 24 → ZMod 2) → ZMod 2 := fun v => d (Classical.choose (hex v))
  have hD : ∀ f ∈ F S S', D (S.vec f.1) = d f := fun f hf =>
    hdep _ (Classical.choose_spec (hex _)).1 f hf (Classical.choose_spec (hex _)).2
  have hDadd : ∀ u v, D (u + v) = D u + D v := by
    intro u v
    obtain ⟨fu, hfu, hu⟩ := hex u
    obtain ⟨fv, hfv, hv⟩ := hex v
    have huv : S.vec (fu * fv).1 = u + v := by
      simp only [Prod.fst_mul]
      rw [S.vec_mul _ _ hfu.1 hfv.1, hu, hv]
    have hDu : D u = d fu := by rw [← hu]; exact hD fu hfu
    have hDv : D v = d fv := by rw [← hv]; exact hD fv hfv
    rw [← huv, hD _ (mul_mem hfu hfv), hd _ hfu _ hfv, ← hDu, ← hDv]
  obtain ⟨a, ha⟩ := Leech.exists_bil₀_eq_of_additive hDadd
  obtain ⟨p, hp, hpa⟩ := S'.vec_surj a
  exact ⟨p, hp, fun f hf => by rw [← hD f hf, ha, hpa]⟩

namespace Glue

variable (G : Glue S S')

def P : Subgroup (H × H') := P0 S S' ⊓ Subgroup.normalizer (G.Δ : Set (H × H'))

theorem mem_P {g : H × H'} :
    g ∈ G.P ↔ g ∈ P0 S S' ∧ ∀ h, h ∈ G.Δ ↔ g * h * g⁻¹ ∈ G.Δ := Iff.rfl

theorem P_le_P0 : G.P ≤ P0 S S' := inf_le_left

theorem conj_mem_Δ {g h : H × H'} (hg : g ∈ G.P) (hh : h ∈ G.Δ) : g * h * g⁻¹ ∈ G.Δ :=
  ((G.mem_P.1 hg).2 h).1 hh

theorem Δ_le_P : G.Δ ≤ G.P := fun _ hg => ⟨F_le_P0 hg.1, Subgroup.le_normalizer hg⟩

theorem mem_P_of_conj [Finite H] [Finite H'] {g : H × H'} (hg : g ∈ P0 S S')
    (h : ∀ n ∈ G.Δ, g * n * g⁻¹ ∈ G.Δ) : g ∈ G.P :=
  ⟨hg, Subgroup.mem_normalizer_fintype h⟩

theorem z1_mem_P : (S.z, (1 : H')) ∈ G.P := by
  refine ⟨S.φ_z.trans (map_one S'.φ).symm, Subgroup.mem_set_normalizer_iff.2 fun h => ?_⟩
  rw [z1_comm h, mul_inv_cancel_right]

theorem m_conj_one {p : H'} (hp : S'.φ p = 1) {f : H × H'} (hf : f ∈ F S S') :
    ((1 : H), p) * f * ((1 : H), p)⁻¹ ∈ F S S' ∧
      G.m (((1 : H), p) * f * ((1 : H), p)⁻¹) =
        G.m f + CFSG.Sporadic.Co1.Module.bil₀ (S'.vec p) (S.vec f.1) := by
  refine ⟨conj_mem_F ?_ hf, ?_⟩
  · show S.φ 1 = S'.φ p
    rw [map_one, hp]
  obtain ⟨a, b⟩ := f
  obtain ⟨h1, h2, h3⟩ := hf
  simp only at h1 h2 h3 ⊢
  have e : ((1 : H), p) * (a, b) * ((1 : H), p)⁻¹ = (a, p * b * p⁻¹) := by simp
  rw [e]
  rcases S'.comm_cases hp h2 with h | h
  · have e2 : p * b * p⁻¹ = b := by
      rw [commutatorElement_eq_one_iff_mul_comm.1 h, mul_inv_cancel_right]
    rw [e2, h3, (S'.comm_eq_one_iff p b hp h2).1 h, add_zero]
  · have e2 : (a, p * b * p⁻¹) = (1, S'.z) * (a, b) := by
      have : p * b * p⁻¹ = S'.z * b := by
        calc p * b * p⁻¹ = (p * b * p⁻¹ * b⁻¹) * b := by group
          _ = S'.z * b := by
            rw [commutatorElement_def] at h
            rw [h]
      simp [this]
    rw [e2, G.m_mul _ one_z_mem_F _ ⟨h1, h2, h3⟩, G.m_one_z, h3,
      (S'.comm_eq_z_iff p b hp h2).1 h, add_comm]

theorem exists_mem_P
    [Finite H] [Finite H'] (x : H) : ∃ y : H', (x, y) ∈ G.P := by
  obtain ⟨y0, hy0⟩ := S'.φ_surj (S.φ x)
  have hg : ((x, y0) : H × H') ∈ P0 S S' := hy0.symm
  set g : H × H' := (x, y0) with hg_def
  have hconj : ∀ f ∈ F S S', g⁻¹ * f * g ∈ F S S' := by
    intro f hf
    have := conj_mem_F (inv_mem hg) hf
    simpa using this
  let d : H × H' → ZMod 2 := fun f => G.m (g⁻¹ * f * g) + G.m f
  have hd : ∀ f₁ ∈ F S S', ∀ f₂ ∈ F S S', d (f₁ * f₂) = d f₁ + d f₂ := by
    intro f₁ h₁ f₂ h₂
    have e : g⁻¹ * (f₁ * f₂) * g = (g⁻¹ * f₁ * g) * (g⁻¹ * f₂ * g) := by group
    simp only [d]
    rw [e, G.m_mul _ (hconj f₁ h₁) _ (hconj f₂ h₂), G.m_mul f₁ h₁ f₂ h₂]
    ring
  have hcentral : ∀ c : H × H', (∀ h, c * h = h * c) → c ∈ F S S' → d c = 0 := by
    intro c hc hcF
    have : g⁻¹ * c * g = c := by
      have := conj_central hc g⁻¹
      simpa using this
    simp only [d]
    rw [this]
    exact CharTwo.add_self_eq_zero _
  obtain ⟨p, hp, hdp⟩ := exists_translation d hd (hcentral _ z1_comm z1_mem_F)
    (hcentral _ one_z_comm one_z_mem_F)
  refine ⟨p * y0, ?_⟩
  have hgg : ((x, p * y0) : H × H') = ((1 : H), p) * g := by simp [hg_def]
  rw [hgg]
  have h1p : ((1 : H), p) ∈ P0 S S' := by
    show S.φ 1 = S'.φ p
    rw [map_one, hp]
  refine G.mem_P_of_conj (mul_mem h1p hg) fun n hn => ?_
  have hnF := hn.1
  have hf₁ : g * n * g⁻¹ ∈ F S S' := conj_mem_F hg hnF
  obtain ⟨hF2, hm2⟩ := G.m_conj_one hp hf₁
  have e : ((1 : H), p) * g * n * (((1 : H), p) * g)⁻¹ =
      ((1 : H), p) * (g * n * g⁻¹) * ((1 : H), p)⁻¹ := by group
  rw [e]
  refine ⟨hF2, ?_⟩
  rw [hm2, ← hdp _ hf₁]
  simp only [d]
  have e3 : g⁻¹ * (g * n * g⁻¹) * g = n := by group
  rw [e3, hn.2, zero_add]
  exact CharTwo.add_self_eq_zero _

theorem eq_of_mem_P_one {y : H'} (h : ((1 : H), y) ∈ G.P) : y = 1 ∨ y = S'.z := by
  have hy : S'.φ y = 1 := by
    have : S.φ 1 = S'.φ y := G.P_le_P0 h
    rw [map_one] at this
    exact this.symm
  refine S'.center_eq y hy fun q hq => ?_
  obtain ⟨a, ha⟩ := G.exists_mem_Δ_snd hq
  have h1 := G.conj_mem_Δ h ha
  have h2 := mul_mem (inv_mem ha) h1
  have e : ((a, q) : H × H')⁻¹ * (((1 : H), y) * (a, q) * ((1 : H), y)⁻¹) =
      (1, q⁻¹ * (y * q * y⁻¹)) := by simp [mul_assoc]
  rw [e] at h2
  have h3 := G.eq_one_of_one_mem_Δ h2
  have h4 : y * q * y⁻¹ = q := by
    rw [inv_mul_eq_one] at h3
    exact h3.symm
  calc q * y = y * q * y⁻¹ * y := by rw [h4]
    _ = y * q := by rw [mul_assoc, inv_mul_cancel, mul_one]

theorem mem_F_of_mem_P {g : H × H'} (hg : g ∈ G.P) (h1 : S.φ g.1 = 1) : g ∈ F S S' := by
  obtain ⟨a, b⟩ := g
  simp only at h1
  obtain ⟨c, hc⟩ := G.exists_mem_Δ_fst h1
  have hcP : ((a, c) : H × H') ∈ G.P := G.Δ_le_P hc
  have h2 : ((a, c) : H × H')⁻¹ * (a, b) ∈ G.P := mul_mem (inv_mem hcP) hg
  have e : ((a, c) : H × H')⁻¹ * (a, b) = (1, c⁻¹ * b) := by simp
  rw [e] at h2
  have hb : S'.φ b = 1 := by
    have : S.φ a = S'.φ b := G.P_le_P0 hg
    rw [← this, h1]
  have hcb : S'.φ (c⁻¹ * b) = 1 := by
    have : S.φ 1 = S'.φ (c⁻¹ * b) := G.P_le_P0 h2
    rw [map_one] at this
    exact this.symm
  have hzero : S'.vec (c⁻¹ * b) = 0 := (S'.vec_eq_zero _ hcb).2 (G.eq_of_mem_P_one h2)
  have hcF := G.Δ_le_F hc
  refine ⟨h1, hb, ?_⟩
  have h5 := S'.vec_mul c (c⁻¹ * b) hcF.2.1 hcb
  rw [mul_inv_cancel_left, hzero, add_zero] at h5
  show S.vec a = S'.vec b
  rw [h5]
  exact hcF.2.2

end Glue

end TypeUnique

end CFSG.Monster.GMS
