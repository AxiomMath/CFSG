module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartOne.SRC

open Subgroup
open scoped commutatorElement

section Normal

variable {Q₁ Q₂ : Type*} [Group Q₁] [Group Q₂]

theorem card_subgroup_prod (H : Subgroup Q₁) (L : Subgroup Q₂) :
    Nat.card (H.prod L) = Nat.card H * Nat.card L := by
  rw [Nat.card_congr (Subgroup.prodEquiv H L).toEquiv, Nat.card_prod]

theorem normal_map_fst (K : Subgroup (Q₁ × Q₂)) [hK : K.Normal] :
    (K.map (MonoidHom.fst Q₁ Q₂)).Normal :=
  Subgroup.Normal.map hK _ (fun a => ⟨(a, 1), rfl⟩)

theorem normal_map_snd (K : Subgroup (Q₁ × Q₂)) [hK : K.Normal] :
    (K.map (MonoidHom.snd Q₁ Q₂)).Normal :=
  Subgroup.Normal.map hK _ (fun b => ⟨(1, b), rfl⟩)

theorem commutator_mem_of_normal {G : Type*} [Group G] (K : Subgroup G) [hK : K.Normal] {k : G}
    (hk : k ∈ K) (g : G) : ⁅k, g⁆ ∈ K := by
  have := mul_mem hk (hK.conj_mem k⁻¹ (inv_mem hk) g)
  rw [commutatorElement_def]
  convert this using 1
  group

theorem inl_mem_of_map_fst_eq_top (hQ₁ : Group.IsPerfect Q₁) (K : Subgroup (Q₁ × Q₂)) [K.Normal]
    (htop : K.map (MonoidHom.fst Q₁ Q₂) = ⊤) : ∀ a : Q₁, (a, 1) ∈ K := by
  have hle : commutator Q₁ ≤ K.comap (MonoidHom.inl Q₁ Q₂) := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ x _
    have ha : a ∈ K.map (MonoidHom.fst Q₁ Q₂) := htop ▸ mem_top a
    obtain ⟨⟨a', b⟩, hk, haa⟩ := Subgroup.mem_map.mp ha
    have haa' : a' = a := haa
    subst haa'
    have h1 := commutator_mem_of_normal K hk ((x, 1) : Q₁ × Q₂)
    rw [Subgroup.mem_comap]
    convert h1 using 1
    simp [commutatorElement_def]
  intro a
  have : a ∈ K.comap (MonoidHom.inl Q₁ Q₂) := by
    apply hle
    rw [hQ₁.commutator_eq_top]
    exact mem_top a
  exact this

theorem inr_mem_of_map_snd_eq_top (hQ₂ : Group.IsPerfect Q₂) (K : Subgroup (Q₁ × Q₂)) [K.Normal]
    (htop : K.map (MonoidHom.snd Q₁ Q₂) = ⊤) : ∀ b : Q₂, (1, b) ∈ K := by
  have hle : commutator Q₂ ≤ K.comap (MonoidHom.inr Q₁ Q₂) := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro b _ y _
    have hb : b ∈ K.map (MonoidHom.snd Q₁ Q₂) := htop ▸ mem_top b
    obtain ⟨⟨a, b'⟩, hk, hbb⟩ := Subgroup.mem_map.mp hb
    have hbb' : b' = b := hbb
    subst hbb'
    have h1 := commutator_mem_of_normal K hk ((1, y) : Q₁ × Q₂)
    rw [Subgroup.mem_comap]
    convert h1 using 1
    simp [commutatorElement_def]
  intro b
  have : b ∈ K.comap (MonoidHom.inr Q₁ Q₂) := by
    apply hle
    rw [hQ₂.commutator_eq_top]
    exact mem_top b
  exact this

theorem normal_prod_left (hQ₂ : CFSG.IsQuasisimple Q₂) (K : Subgroup (Q₁ × Q₂)) [K.Normal]
    (hK : ∀ a : Q₁, (a, 1) ∈ K) :
    K = ⊤ ∨ K ≤ (⊤ : Subgroup Q₁).prod (center Q₂) := by
  have := normal_map_snd K
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ₂ this with htop | hle
  · left
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have hb : b ∈ K.map (MonoidHom.snd Q₁ Q₂) := htop ▸ mem_top b
    obtain ⟨⟨a', b'⟩, hk, hbb⟩ := Subgroup.mem_map.mp hb
    have hbb' : b' = b := hbb
    subst hbb'
    have : ((a, b') : Q₁ × Q₂) = (a * a'⁻¹, 1) * (a', b') := by simp
    rw [this]
    exact mul_mem (hK _) hk
  · right
    rintro ⟨a, b⟩ hab
    exact Subgroup.mem_prod.mpr ⟨mem_top a, hle ⟨(a, b), hab, rfl⟩⟩

theorem normal_prod_right (hQ₁ : CFSG.IsQuasisimple Q₁) (K : Subgroup (Q₁ × Q₂)) [K.Normal]
    (hK : ∀ b : Q₂, (1, b) ∈ K) :
    K = ⊤ ∨ K ≤ (center Q₁).prod (⊤ : Subgroup Q₂) := by
  have := normal_map_fst K
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ₁ this with htop | hle
  · left
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have ha : a ∈ K.map (MonoidHom.fst Q₁ Q₂) := htop ▸ mem_top a
    obtain ⟨⟨a', b'⟩, hk, haa⟩ := Subgroup.mem_map.mp ha
    have haa' : a' = a := haa
    subst haa'
    have : ((a', b) : Q₁ × Q₂) = (1, b * b'⁻¹) * (a', b') := by simp
    rw [this]
    exact mul_mem (hK _) hk
  · right
    rintro ⟨a, b⟩ hab
    exact Subgroup.mem_prod.mpr ⟨hle ⟨(a, b), hab, rfl⟩, mem_top b⟩

theorem normal_prod_trichotomy (hQ₁ : CFSG.IsQuasisimple Q₁) (hQ₂ : CFSG.IsQuasisimple Q₂)
    (K : Subgroup (Q₁ × Q₂)) [K.Normal] :
    (∀ a : Q₁, (a, 1) ∈ K) ∨ (∀ b : Q₂, (1, b) ∈ K) ∨
      K ≤ (center Q₁).prod (center Q₂) := by
  have h1 := normal_map_fst K
  have h2 := normal_map_snd K
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ₁ h1 with htop1 | hle1
  · exact Or.inl (inl_mem_of_map_fst_eq_top hQ₁.1 K htop1)
  · rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ₂ h2 with htop2 | hle2
    · exact Or.inr (Or.inl (inr_mem_of_map_snd_eq_top hQ₂.1 K htop2))
    · refine Or.inr (Or.inr ?_)
      rintro ⟨a, b⟩ hab
      exact Subgroup.mem_prod.mpr ⟨hle1 ⟨(a, b), hab, rfl⟩, hle2 ⟨(a, b), hab, rfl⟩⟩

variable [Finite Q₁] [Finite Q₂]

theorem eq_top_of_card_dvd_prod (hQ₁ : CFSG.IsQuasisimple Q₁) (hQ₂ : CFSG.IsQuasisimple Q₂)
    {g m m₁ m₂ : ℕ} (hm : m ∣ Nat.card Q₁ * Nat.card Q₂)
    (hmc : Nat.Coprime m (Nat.card (center Q₁) * Nat.card (center Q₂))) (hmg : ¬ m ∣ g)
    (hm₁ : m₁ ∣ Nat.card Q₁) (hm₁c : Nat.Coprime m₁ (Nat.card (center Q₁))) (hm₁g : ¬ m₁ ∣ g)
    (hm₂ : m₂ ∣ Nat.card Q₂) (hm₂c : Nat.Coprime m₂ (Nat.card (center Q₂))) (hm₂g : ¬ m₂ ∣ g)
    (K : Subgroup (Q₁ × Q₂)) [K.Normal]
    (hK : Nat.card Q₁ * Nat.card Q₂ ∣ Nat.card K * g) : K = ⊤ := by
  have hQ₁pos : 0 < Nat.card Q₁ := Nat.card_pos
  have hQ₂pos : 0 < Nat.card Q₂ := Nat.card_pos
  rcases normal_prod_trichotomy hQ₁ hQ₂ K with hl | hr | hc
  · rcases normal_prod_left hQ₂ K hl with htop | hle
    · exact htop
    · exfalso
      have hKd : Nat.card K ∣ Nat.card Q₁ * Nat.card (center Q₂) := by
        have := Subgroup.card_dvd_of_le hle
        rwa [card_subgroup_prod, Subgroup.card_top] at this
      have h1 : Nat.card Q₁ * Nat.card Q₂ ∣ Nat.card Q₁ * (Nat.card (center Q₂) * g) := by
        refine hK.trans ?_
        rw [← mul_assoc]
        exact Nat.mul_dvd_mul_right hKd g
      have h2 := (Nat.mul_dvd_mul_iff_left hQ₁pos).mp h1
      exact hm₂g (hm₂c.dvd_of_dvd_mul_left (hm₂.trans h2))
  · rcases normal_prod_right hQ₁ K hr with htop | hle
    · exact htop
    · exfalso
      have hKd : Nat.card K ∣ Nat.card (center Q₁) * Nat.card Q₂ := by
        have := Subgroup.card_dvd_of_le hle
        rwa [card_subgroup_prod, Subgroup.card_top] at this
      have h1 : Nat.card Q₁ * Nat.card Q₂ ∣ (Nat.card (center Q₁) * g) * Nat.card Q₂ := by
        refine hK.trans ?_
        have : Nat.card (center Q₁) * g * Nat.card Q₂ = Nat.card (center Q₁) * Nat.card Q₂ * g := by
          ring
        rw [this]
        exact Nat.mul_dvd_mul_right hKd g
      have h2 := (Nat.mul_dvd_mul_iff_right hQ₂pos).mp h1
      exact hm₁g (hm₁c.dvd_of_dvd_mul_left (hm₁.trans h2))
  · exfalso
    have hKd : Nat.card K ∣ Nat.card (center Q₁) * Nat.card (center Q₂) := by
      have := Subgroup.card_dvd_of_le hc
      rwa [card_subgroup_prod] at this
    have h1 : m ∣ Nat.card K * g := (hm.trans hK)
    exact hmg ((Nat.Coprime.coprime_dvd_right hKd hmc).dvd_of_dvd_mul_left h1)

omit [Finite Q₁] [Finite Q₂] in
theorem eq_top_of_coprime_elements (hQ₁ : CFSG.IsQuasisimple Q₁) (hQ₂ : CFSG.IsQuasisimple Q₂)
    {p : ℕ} {h₁ : Q₁} (hh₁ : h₁ ∉ center Q₁) (ho₁ : Nat.Coprime (orderOf h₁) p) {h₂ : Q₂}
    (hh₂ : h₂ ∉ center Q₂) (ho₂ : Nat.Coprime (orderOf h₂) p) (N : Subgroup (Q₁ × Q₂))
    [N.Normal] (hN : ∀ h : Q₁ × Q₂, Nat.Coprime (orderOf h) p → h ∈ N) : N = ⊤ := by
  have hinl : ∀ a : Q₁, (a, 1) ∈ N := by
    have hn : (N.comap (MonoidHom.inl Q₁ Q₂)).Normal := inferInstance
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ₁ hn with htop | hle
    · intro a
      have : a ∈ N.comap (MonoidHom.inl Q₁ Q₂) := htop ▸ mem_top a
      exact this
    · exfalso
      apply hh₁
      apply hle
      change ((h₁, 1) : Q₁ × Q₂) ∈ N
      refine hN _ ?_
      have := orderOf_injective (MonoidHom.inl Q₁ Q₂) (fun a b h => (Prod.ext_iff.mp h).1) h₁
      change Nat.Coprime (orderOf (MonoidHom.inl Q₁ Q₂ h₁)) p
      rwa [this]
  have hinr : ∀ b : Q₂, (1, b) ∈ N := by
    have hn : (N.comap (MonoidHom.inr Q₁ Q₂)).Normal := inferInstance
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ₂ hn with htop | hle
    · intro b
      have : b ∈ N.comap (MonoidHom.inr Q₁ Q₂) := htop ▸ mem_top b
      exact this
    · exfalso
      apply hh₂
      apply hle
      change ((1, h₂) : Q₁ × Q₂) ∈ N
      refine hN _ ?_
      have := orderOf_injective (MonoidHom.inr Q₁ Q₂) (fun a b h => (Prod.ext_iff.mp h).2) h₂
      change Nat.Coprime (orderOf (MonoidHom.inr Q₁ Q₂ h₂)) p
      rwa [this]
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  have := mul_mem (hinl a) (hinr b)
  simpa using this

end Normal

end CFSG.RankThree.PartOne.SRC
