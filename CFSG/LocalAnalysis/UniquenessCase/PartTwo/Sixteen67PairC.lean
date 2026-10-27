module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67PairB
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Cfg1667

variable {M V W₁ W₂ : Subgroup G} {g : G}

private theorem exists_mul_of_mem_sup {W₁ W₂ : Subgroup G}
    (hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a) {v : G}
    (hv : v ∈ W₁ ⊔ W₂) : ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, w₁ * w₂ = v := by
  rw [Subgroup.sup_eq_closure] at hv
  refine Subgroup.closure_induction (p := fun v _ => ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, w₁ * w₂ = v)
    ?_ ?_ ?_ ?_ hv
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, W₂.one_mem, by simp⟩
    · exact ⟨1, W₁.one_mem, x, hx, by simp⟩
  · exact ⟨1, W₁.one_mem, 1, W₂.one_mem, by simp⟩
  · rintro x y hx hy ⟨a₁, ha₁, a₂, ha₂, rfl⟩ ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    exact ⟨a₁ * b₁, W₁.mul_mem ha₁ hb₁, a₂ * b₂, W₂.mul_mem ha₂ hb₂, by
      calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
        _ = a₁ * (a₂ * b₁) * b₂ := by rw [hcomm b₁ hb₁ a₂ ha₂]
        _ = a₁ * a₂ * (b₁ * b₂) := by group⟩
  · rintro x hx ⟨a₁, ha₁, a₂, ha₂, rfl⟩
    exact ⟨a₁⁻¹, W₁.inv_mem ha₁, a₂⁻¹, W₂.inv_mem ha₂,
      by rw [← mul_inv_rev a₂ a₁, hcomm a₁ ha₁ a₂ ha₂]⟩

private theorem mul_eq_mul_iff {W₁ W₂ : Subgroup G} (hinf : W₁ ⊓ W₂ = ⊥)
    {a₁ a₂ b₁ b₂ : G} (ha₁ : a₁ ∈ W₁) (ha₂ : a₂ ∈ W₂) (hb₁ : b₁ ∈ W₁) (hb₂ : b₂ ∈ W₂) :
    a₁ * a₂ = b₁ * b₂ ↔ a₁ = b₁ ∧ a₂ = b₂ := by
  constructor
  · intro h
    have hmem : b₁⁻¹ * a₁ = b₂ * a₂⁻¹ := by
      calc b₁⁻¹ * a₁ = b₁⁻¹ * (a₁ * a₂) * a₂⁻¹ := by group
        _ = b₁⁻¹ * (b₁ * b₂) * a₂⁻¹ := by rw [h]
        _ = b₂ * a₂⁻¹ := by group
    have h1 : b₁⁻¹ * a₁ ∈ W₁ := W₁.mul_mem (W₁.inv_mem hb₁) ha₁
    have h2 : b₂ * a₂⁻¹ ∈ W₂ := W₂.mul_mem hb₂ (W₂.inv_mem ha₂)
    have hbot : b₁⁻¹ * a₁ = 1 := by
      have : b₁⁻¹ * a₁ ∈ W₁ ⊓ W₂ := ⟨h1, by rw [hmem]; exact h2⟩
      rw [hinf] at this
      exact Subgroup.mem_bot.mp this
    have ha₁eq : a₁ = b₁ := by
      have h' : b₁ * (b₁⁻¹ * a₁) = b₁ * 1 := congrArg (fun t => b₁ * t) hbot
      calc a₁ = b₁ * (b₁⁻¹ * a₁) := by group
        _ = b₁ * 1 := h'
        _ = b₁ := by rw [mul_one]
    have h2' : a₁ * a₂ = a₁ * b₂ := by rw [h, ha₁eq]
    exact ⟨ha₁eq, mul_left_cancel h2'⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem card_sup_of_commute_of_inf_eq_bot (L R : Subgroup G)
    (hcomm : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) (hinf : L ⊓ R = ⊥) :
    Nat.card (L ⊔ R : Subgroup G) = Nat.card L * Nat.card R := by
  let f : ↥L × ↥R → ↥(L ⊔ R) := fun p =>
    ⟨(p.1 : G) * (p.2 : G),
      mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
      have hG : (x₁ : G) * (y₁ : G) = (x₂ : G) * (y₂ : G) := congrArg Subtype.val h
      have huniq := (mul_eq_mul_iff hinf x₁.2 y₁.2 x₂.2 y₂.2).mp hG
      exact Prod.ext (Subtype.ext huniq.1) (Subtype.ext huniq.2)
    · intro z
      obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_of_mem_sup hcomm z.2
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Subtype.ext hxy⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

private theorem card_inf_centralizer_zpowers_eq_two {W : Subgroup G} {t : G}
    (hcard : Nat.card W = 4) (ht2 : t ^ 2 = 1) (htN : t ∈ Subgroup.normalizer (W : Set G))
    (htC : t ∉ Subgroup.centralizer (W : Set G)) :
    Nat.card (W ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G) : Subgroup G) = 2 := by
  set F : Subgroup G := W ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G) with hF
  have hFW : F ≤ W := inf_le_left
  have hW2 : IsPGroup 2 ↥W := IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num)
  have hWne : W ≠ ⊥ := by
    intro h; rw [h] at hcard; simp at hcard
  have hS2 : IsPGroup 2 ↥(Subgroup.zpowers t) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one ht2
  have hSN : Subgroup.zpowers t ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.zpowers_le.mpr htN
  obtain ⟨x, hxW, hx1, hxcent⟩ :=
    CFSG.AGLEmbeddingD2.McLaughlin.exists_ne_one_centralized_of_isPGroup_two hS2 hSN hW2 hWne
  have hFne : F ≠ ⊥ := by
    intro hbot
    have hxF : x ∈ F := by
      refine ⟨hxW, Subgroup.mem_centralizer_iff.mpr ?_⟩
      exact hxcent
    rw [hbot] at hxF
    exact hx1 (Subgroup.mem_bot.mp hxF)
  have hFWne : F ≠ W := by
    intro hEq
    have htcent : t ∈ Subgroup.centralizer (W : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hwF : w ∈ F := hEq ▸ hw
      exact (Subgroup.mem_centralizer_iff.mp hwF.2 t (Subgroup.mem_zpowers t)).symm
    exact htC htcent
  have hdvd : Nat.card F ∣ 4 := by
    have h := Subgroup.relIndex_mul_card F W
    rw [inf_eq_left.mpr hFW, hcard] at h
    exact ⟨F.relIndex W, by rw [← h, mul_comm]⟩
  have hle : Nat.card F ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hne1 : Nat.card F ≠ 1 := by
    intro h1
    exact hFne (Subgroup.eq_bot_of_card_le (H := F) (by omega))
  have hne4 : Nat.card F ≠ 4 := by
    intro h4
    exact hFWne (Subgroup.eq_of_le_of_card_ge hFW (by rw [hcard, h4]))
  have hpos : 0 < Nat.card F := Nat.card_pos
  interval_cases Nat.card F
  · exact absurd rfl hne1
  · rfl
  · exact absurd hdvd (by norm_num)
  · exact absurd rfl hne4

private theorem mem_centralizer_sup {W₁ W₂ V : Subgroup G} (hsup : W₁ ⊔ W₂ = V) {a : G}
    (h₁ : a ∈ Subgroup.centralizer (W₁ : Set G)) (h₂ : a ∈ Subgroup.centralizer (W₂ : Set G)) :
    a ∈ Subgroup.centralizer (V : Set G) := by
  have h1 : W₁ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp h₁ y hy
  have h2 : W₂ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp h₂ y hy
  have hV : V ≤ Subgroup.centralizer ({a} : Set G) := hsup ▸ sup_le h1 h2
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' := hV hv
  rwa [Subgroup.mem_centralizer_singleton_iff] at hv'

private theorem centralizer_zpowers_eq_centralizer_singleton (t : G) :
    Subgroup.centralizer (Subgroup.zpowers t : Set G) = Subgroup.centralizer ({t} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

private theorem mem_centralizer_of_conj {A B : Subgroup G} {b s : G} (hsb : s * b = b * s)
    (hswap : conjSubgroup A s = B) (hcent : b ∈ Subgroup.centralizer (A : Set G)) :
    b ∈ Subgroup.centralizer (B : Set G) := by
  have hsbs : s * b * s⁻¹ = b := by rw [hsb]; group
  have hmem : b ∈ conjSubgroup (Subgroup.centralizer (A : Set G)) s := by
    rw [mem_conjSubgroup_iff, hsbs]
    exact hcent
  rwa [E3.conjSubgroup_centralizer, hswap] at hmem

private theorem card_subgroupOf_of_le {H K : Subgroup G} (h : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H := by
  rw [← Subgroup.card_subtype K (H.subgroupOf K), Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr h]

private theorem commutator_mul_of_mem_B (h : Cfg1667 M V W₁ W₂) {b : G}
    (hb : b ∈ conjSubgroup V g ⊓ M) {x y : G} (hx : x ∈ V) (hy : y ∈ V) :
    x * y * b * (x * y)⁻¹ * b⁻¹ =
      (x * b * x⁻¹ * b⁻¹) * (y * b * y⁻¹ * b⁻¹) := by
  have hbnorm : b ∈ normalizer (V : Set G) := by rw [h.normalizer_eq]; exact hb.2
  have hzV : b * x⁻¹ * b⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.1 hbnorm x⁻¹).1 (V.inv_mem hx)
  have hzy : (b * x⁻¹ * b⁻¹) * y = y * (b * x⁻¹ * b⁻¹) :=
    IsElemAbelian.comm h.elemAbelian hzV hy
  have hxy : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ :=
    IsElemAbelian.comm h.elemAbelian (V.inv_mem hx) (V.inv_mem hy)
  calc x * y * b * (x * y)⁻¹ * b⁻¹
      = x * y * b * (y⁻¹ * x⁻¹) * b⁻¹ := by rw [mul_inv_rev]
    _ = x * y * b * (x⁻¹ * y⁻¹) * b⁻¹ := by rw [← hxy]
    _ = (x * b * x⁻¹ * b⁻¹) * (y * b * y⁻¹ * b⁻¹) := by
          rw [show (x * b * x⁻¹ * b⁻¹) * (y * b * y⁻¹ * b⁻¹)
                = x * ((b * x⁻¹ * b⁻¹) * y) * b * y⁻¹ * b⁻¹ by group,
              hzy]
          group

private theorem mem_commutator_of_relIndex_two (h : Cfg1667 M V W₁ W₂)
    (hg : InCalO 1 M ⊥ V g) {v b : G} (hv : v ∈ V) (hvU : v ∉ V ⊓ conjSubgroup M g)
    (hb : b ∈ conjSubgroup V g ⊓ M)
    (hcv : v * b * v⁻¹ * b⁻¹ ∈ V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M)) :
    ∀ w ∈ V, w * b * w⁻¹ * b⁻¹ ∈ V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) := by
  intro w hw
  have hindex : ((V ⊓ conjSubgroup M g).subgroupOf V).index = 2 := relIndex_U h hg
  by_cases hwU : w ∈ V ⊓ conjSubgroup M g
  · have hmem := (Subgroup.commutator_le.mp (commutator_U_B_le h hg)) w hwU b hb
    rwa [commutatorElement_def] at hmem
  · have hvu : v⁻¹ * w ∈ V ⊓ conjSubgroup M g := by
      by_contra hnot
      have hvU' : (⟨v, hv⟩ : V) ∉ (V ⊓ conjSubgroup M g).subgroupOf V :=
        fun hh => hvU (Subgroup.mem_subgroupOf.mp hh)
      have hb' : (⟨v⁻¹ * w, V.mul_mem (V.inv_mem hv) hw⟩ : V) ∉
          (V ⊓ conjSubgroup M g).subgroupOf V :=
        fun hh => hnot (Subgroup.mem_subgroupOf.mp hh)
      have hmem := (Subgroup.mul_mem_iff_of_index_two
        (H := (V ⊓ conjSubgroup M g).subgroupOf V) hindex
        (a := (⟨v, hv⟩ : V)) (b := (⟨v⁻¹ * w, V.mul_mem (V.inv_mem hv) hw⟩ : V))).mpr
        (iff_of_false hvU' hb')
      have hwmem : (⟨w, hw⟩ : V) ∈ (V ⊓ conjSubgroup M g).subgroupOf V := by
        have hEq : (⟨v, hv⟩ : V) * (⟨v⁻¹ * w, V.mul_mem (V.inv_mem hv) hw⟩ : V) =
            (⟨w, hw⟩ : V) := by
          apply Subtype.ext
          simp [mul_assoc]
        rwa [hEq] at hmem
      exact (fun hh => hwU (Subgroup.mem_subgroupOf.mp hh)) hwmem
    have hvu' : v⁻¹ * w ∈ V := hvu.1
    have hsplit : w * b * w⁻¹ * b⁻¹ =
        (v * b * v⁻¹ * b⁻¹) * ((v⁻¹ * w) * b * (v⁻¹ * w)⁻¹ * b⁻¹) := by
      conv_lhs => rw [show w = v * (v⁻¹ * w) by group]
      exact commutator_mul_of_mem_B h hb hv hvu'
    rw [hsplit]
    refine mul_mem hcv ?_
    have hmem := (Subgroup.commutator_le.mp (commutator_U_B_le h hg)) (v⁻¹ * w) hvu b hb
    rwa [commutatorElement_def] at hmem

theorem card_centralizer_of_mem_B (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) {b : G}
    (hb : b ∈ conjSubgroup V g ⊓ M) (hbV : b ∉ centralizer (V : Set G)) :
    Nat.card (V ⊓ centralizer ({b} : Set G) : Subgroup G) = 4 := by
  have hB : IsElemAbelian 2 (conjSubgroup V g ⊓ M) :=
    (E3.isElemAbelian_conjSubgroup h.elemAbelian g).mono inf_le_left
  have hb2 : b * b = 1 := IsElemAbelian.mul_self_eq_one hB hb
  have hb2pow : b ^ 2 = 1 := by rw [pow_two]; exact hb2
  rcases h.perm b hb.2 with ⟨hb1, hb2'⟩ | ⟨hb1, hb2'⟩
  · have hbN₁ : b ∈ normalizer (W₁ : Set G) := conjSubgroup_eq_iff_mem_normalizer.mp hb1
    have hbN₂ : b ∈ normalizer (W₂ : Set G) := conjSubgroup_eq_iff_mem_normalizer.mp hb2'
    obtain ⟨s, hsB, hs₁, hs₂⟩ := exists_swap h hg
    have hsb : s * b = b * s := IsElemAbelian.comm hB hsB hb
    have hbC₁ : b ∉ centralizer (W₁ : Set G) := by
      intro hbc
      exact hbV (mem_centralizer_sup h.sup_eq hbc (mem_centralizer_of_conj hsb hs₁ hbc))
    have hbC₂ : b ∉ centralizer (W₂ : Set G) := by
      intro hbc
      exact hbV (mem_centralizer_sup h.sup_eq (mem_centralizer_of_conj hsb hs₂ hbc) hbc)
    have hcard₁ := card_inf_centralizer_zpowers_eq_two (W := W₁) h.card₁ hb2pow hbN₁ hbC₁
    have hcard₂ := card_inf_centralizer_zpowers_eq_two (W := W₂) h.card₂ hb2pow hbN₂ hbC₂
    rw [centralizer_zpowers_eq_centralizer_singleton b] at hcard₁ hcard₂
    have hW₁V : W₁ ≤ V := by rw [← h.sup_eq]; exact le_sup_left
    have hW₂V : W₂ ≤ V := by rw [← h.sup_eq]; exact le_sup_right
    have hsup : (W₁ ⊓ centralizer ({b} : Set G)) ⊔ (W₂ ⊓ centralizer ({b} : Set G)) =
        V ⊓ centralizer ({b} : Set G) := by
      refine le_antisymm ?_ ?_
      · exact sup_le (le_inf (inf_le_left.trans hW₁V) inf_le_right)
          (le_inf (inf_le_left.trans hW₂V) inf_le_right)
      · intro x hx
        obtain ⟨hxV, hxC⟩ := Subgroup.mem_inf.mp hx
        obtain ⟨w₁, hw₁, w₂, hw₂, hw₁w₂⟩ := exists_mul_of_mem_sup (W₁ := W₁) (W₂ := W₂) (v := x)
          (fun a ha c hc => IsElemAbelian.comm h.elemAbelian (hW₁V ha) (hW₂V hc))
          (by rw [h.sup_eq]; exact hxV)
        have hxfix : b * x * b⁻¹ = x := by
          rw [mul_inv_eq_iff_eq_mul]
          exact (Subgroup.mem_centralizer_singleton_iff.mp hxC).symm
        have hbw₁ : b * w₁ * b⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.1 hbN₁ w₁).1 hw₁
        have hbw₂ : b * w₂ * b⁻¹ ∈ W₂ := (Subgroup.mem_normalizer_iff.1 hbN₂ w₂).1 hw₂
        have hprod : (b * w₁ * b⁻¹) * (b * w₂ * b⁻¹) = w₁ * w₂ := by
          calc (b * w₁ * b⁻¹) * (b * w₂ * b⁻¹) = b * (w₁ * w₂) * b⁻¹ := by group
            _ = b * x * b⁻¹ := by rw [hw₁w₂]
            _ = x := hxfix
            _ = w₁ * w₂ := hw₁w₂.symm
        obtain ⟨hbw₁eq, hbw₂eq⟩ := (mul_eq_mul_iff h.inf_eq hbw₁ hbw₂ hw₁ hw₂).mp hprod
        have hw₁C : w₁ ∈ W₁ ⊓ centralizer ({b} : Set G) :=
          ⟨hw₁, Subgroup.mem_centralizer_singleton_iff.mpr
            (mul_inv_eq_iff_eq_mul.mp hbw₁eq).symm⟩
        have hw₂C : w₂ ∈ W₂ ⊓ centralizer ({b} : Set G) :=
          ⟨hw₂, Subgroup.mem_centralizer_singleton_iff.mpr
            (mul_inv_eq_iff_eq_mul.mp hbw₂eq).symm⟩
        rw [← hw₁w₂]
        exact mul_mem (Subgroup.mem_sup_left hw₁C) (Subgroup.mem_sup_right hw₂C)
    have hinf : (W₁ ⊓ centralizer ({b} : Set G)) ⊓ (W₂ ⊓ centralizer ({b} : Set G)) = ⊥ := by
      have hle : (W₁ ⊓ centralizer ({b} : Set G)) ⊓ (W₂ ⊓ centralizer ({b} : Set G)) ≤
          W₁ ⊓ W₂ :=
        le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
      rw [h.inf_eq] at hle
      exact le_antisymm hle bot_le
    have hcard := card_sup_of_commute_of_inf_eq_bot _ _
      (fun x hx y hy => IsElemAbelian.comm h.elemAbelian
        ((inf_le_left.trans hW₁V) hx) ((inf_le_left.trans hW₂V) hy)) hinf
    rw [← hsup, hcard, hcard₁, hcard₂]
  · exact card_centralizer_swap h hb2 hb1 hb2'

theorem mem_of_commutator_mem (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) {v b : G}
    (hv : v ∈ V) (hvU : v ∉ V ⊓ conjSubgroup M g) (hb : b ∈ conjSubgroup V g ⊓ M)
    (hc : v * b * v⁻¹ * b⁻¹ ∈ V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M)) :
    b ∈ V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) := by
  by_contra hbnot
  have hbV : b ∉ centralizer (V : Set G) := by
    intro hbc
    exact hbnot (by rw [← B_inf_centralizer_eq h hg]; exact ⟨hb, hbc⟩)
  have hcardC : Nat.card (V ⊓ centralizer ({b} : Set G) : Subgroup G) = 4 :=
    card_centralizer_of_mem_B h hg hb hbV
  let f : V →* V :=
    MonoidHom.mk' (fun w : V => ⟨(w : G) * b * (w : G)⁻¹ * b⁻¹, by
      have hbnorm : b ∈ normalizer (V : Set G) := by rw [h.normalizer_eq]; exact hb.2
      have hbw : b * (w : G)⁻¹ * b⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.1 hbnorm (w : G)⁻¹).1 (V.inv_mem w.2)
      simpa only [mul_assoc] using V.mul_mem w.2 hbw⟩)
      (by
        intro x y
        apply Subtype.ext
        exact commutator_mul_of_mem_B h hb x.2 y.2)
  have hker : f.ker = (V ⊓ centralizer ({b} : Set G)).subgroupOf V := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hw
      have hw' : ⁅(w : G), b⁆ = 1 := by
        rw [commutatorElement_def]
        exact Subtype.ext_iff.mp hw
      exact ⟨w.2, commutatorElement_eq_one_iff_mul_comm.mp hw'⟩
    · rintro ⟨_, hcent⟩
      apply Subtype.ext
      have hw' : ⁅(w : G), b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcent
      rwa [commutatorElement_def] at hw'
  have hcardker : Nat.card f.ker = 4 := by
    rw [hker, card_subgroupOf_of_le inf_le_left]
    exact hcardC
  have hrange_le : f.range ≤
      (V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M)).subgroupOf V := by
    rintro _ ⟨w, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact mem_commutator_of_relIndex_two h hg hv hvU hb hc w w.2
  have hcardrange : Nat.card f.range = 4 := by
    have hcm := Subgroup.card_ker_mul_card_range f
    rw [hcardker, h.card_V] at hcm
    omega
  have hle := Subgroup.card_le_of_le hrange_le
  rw [hcardrange] at hle
  have hUle : V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) ≤ V :=
    inf_le_left.trans inf_le_left
  have hUcard : Nat.card ((V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M)).subgroupOf V) = 2 := by
    rw [card_subgroupOf_of_le hUle, card_U_inf_B h hg]
  rw [hUcard] at hle
  exact absurd hle (by norm_num)

theorem mem_of_commutator_mem' (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) {i a : G}
    (hi : i ∈ conjSubgroup V g) (hiB : i ∉ conjSubgroup V g ⊓ M) (ha : a ∈ V ⊓ conjSubgroup M g)
    (hc : i * a * i⁻¹ * a⁻¹ ∈ V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M)) :
    a ∈ V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) := by
  have hmain := mem_of_commutator_mem (h.conj g) (inCalO_bot_swap hg)
    (v := i) (b := a)
    (by simpa only [conjSubgroup_conjSubgroup_inv] using hi)
    (by simpa only [conjSubgroup_conjSubgroup_inv] using hiB)
    (by simpa only [conjSubgroup_conjSubgroup_inv] using ha)
    (by
      have h1 : i * a * i⁻¹ * a⁻¹ ∈ V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) := hc
      rw [inf_comm (V ⊓ conjSubgroup M g) (conjSubgroup V g ⊓ M)] at h1
      simpa only [conjSubgroup_conjSubgroup_inv] using h1)
  simpa only [conjSubgroup_conjSubgroup_inv,
    inf_comm (conjSubgroup V g ⊓ M) (V ⊓ conjSubgroup M g)] using hmain

end Cfg1667

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
