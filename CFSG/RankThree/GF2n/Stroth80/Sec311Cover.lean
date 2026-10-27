module

public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {R : Type} [Group R]

theorem map_le_center_of_comm (N N₀ L : Subgroup R) [N₀.Normal]
    (hgen : ⨆ g : R, conjSubgroup g L = ⊤)
    (hcomm : ∀ (g : R), ∀ n ∈ N, ∀ l ∈ conjSubgroup g L, ⁅n, l⁆ ∈ N₀) :
    N.map (QuotientGroup.mk' N₀) ≤ Subgroup.center (R ⧸ N₀) := by
  set π₀ := QuotientGroup.mk' N₀ with hπ₀
  have hC : (⊤ : Subgroup R) ≤
      (Subgroup.centralizer ((N.map π₀ : Subgroup (R ⧸ N₀)) : Set (R ⧸ N₀))).comap π₀ := by
    rw [← hgen]
    refine iSup_le fun g => ?_
    intro l hl
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    rintro y ⟨n, hn, rfl⟩
    rw [hπ₀, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
    have := hcomm g n hn l hl
    have e : n * l / (l * n) = ⁅n, l⁆ := by
      rw [commutatorElement_def, div_eq_mul_inv, mul_inv_rev]; simp only [mul_assoc]
    rw [e]
    exact this
  rintro z ⟨n, hn, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro x
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective x
  have := Subgroup.mem_centralizer_iff.mp (hC (Subgroup.mem_top r)) (π₀ n) ⟨n, hn, rfl⟩
  exact this.symm

theorem isElemAbelian_map_of_ab (N N₀ L : Subgroup R) [N₀.Normal]
    (hLN : L ⊓ N ≤ N₀) (hN₀N : N₀ ≤ N)
    (hab : ∀ l ∈ L, ∀ l' ∈ L, ⁅l, l'⁆ ∈ N ∧ l ^ 2 ∈ N) :
    IsElemAbelian 2 (L.map (QuotientGroup.mk' N₀)) := by
  have hmem : ∀ x ∈ L, x ∈ N → x ∈ N₀ := fun x hx hxN => hLN ⟨hx, hxN⟩
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    show QuotientGroup.mk' N₀ a * QuotientGroup.mk' N₀ b =
      QuotientGroup.mk' N₀ b * QuotientGroup.mk' N₀ a
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
    have hc := hmem _ (L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb))
      (by simpa [commutatorElement_def] using (hab a ha b hb).1)
    have e : a * b / (b * a) = a * b * a⁻¹ * b⁻¹ := by
      rw [div_eq_mul_inv, mul_inv_rev]; simp only [mul_assoc]
    rw [e]
    exact hc
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hmem _ (L.pow_mem ha 2) (hab a ha a ha).2

theorem commutator_eq_top_of_root [Finite R] (N N₀ L : Subgroup R) [N₀.Normal]
    (hN₀N : N₀ ≤ N) (hgen : ⨆ g : R, conjSubgroup g L = ⊤) (hLN : L ⊓ N ≤ N₀)
    (hab : ∀ l ∈ L, ∀ l' ∈ L, ⁅l, l'⁆ ∈ N ∧ l ^ 2 ∈ N) {τ : R}
    (hτL : τ ∈ Subgroup.normalizer (L : Set R)) (hτ : ∀ l ∈ L, ⁅τ, l⁆ ∈ N → l ∈ N) :
    commutator (R ⧸ N₀) = ⊤ := by
  set π₀ := QuotientGroup.mk' N₀ with hπ₀
  set A := L.map π₀ with hA
  have hAab := isElemAbelian_map_of_ab N N₀ L hLN hN₀N hab
  have hτA : ∀ a ∈ A, π₀ τ * a * (π₀ τ)⁻¹ ∈ A := by
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨τ * l * τ⁻¹, ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.mp hτL l).mp hl
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAab.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  let δ : ↥A →* ↥A :=
    { toFun := fun a => ⟨⁅π₀ τ, (a : R ⧸ N₀)⁆, by
        rw [commutatorElement_def]
        exact A.mul_mem (hτA _ a.2) (A.inv_mem a.2)⟩
      map_one' := by
        apply Subtype.ext
        simp [commutatorElement_def]
      map_mul' := by
        intro a b
        apply Subtype.ext
        have hv : π₀ τ * (b : R ⧸ N₀) * (π₀ τ)⁻¹ * (b : R ⧸ N₀)⁻¹ ∈ A :=
          A.mul_mem (hτA _ b.2) (A.inv_mem b.2)
        have key := hcomm _ hv _ (A.inv_mem a.2)
        simp only [Subgroup.coe_mul, commutatorElement_def, mul_inv_rev]
        calc π₀ τ * (↑a * ↑b) * (π₀ τ)⁻¹ * ((↑b)⁻¹ * (↑a)⁻¹)
            = (π₀ τ * ↑a * (π₀ τ)⁻¹) *
              ((π₀ τ * ↑b * (π₀ τ)⁻¹ * (↑b)⁻¹) * (↑a)⁻¹) := by
              group
          _ = (π₀ τ * ↑a * (π₀ τ)⁻¹) *
              ((↑a)⁻¹ * (π₀ τ * ↑b * (π₀ τ)⁻¹ * (↑b)⁻¹)) := by
              rw [key]
          _ = (π₀ τ * ↑a * (π₀ τ)⁻¹ * (↑a)⁻¹) * (π₀ τ * ↑b * (π₀ τ)⁻¹ * (↑b)⁻¹) := by
              group }
  have hinj : Function.Injective δ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨l, hl, hla⟩ := a.2
    have h1 : ⁅π₀ τ, (a : R ⧸ N₀)⁆ = 1 := congrArg Subtype.val ha
    rw [← hla, ← map_commutatorElement] at h1
    have h2 : ⁅τ, l⁆ ∈ N₀ := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : l ∈ N := hτ l hl (hN₀N h2)
    apply Subtype.ext
    show (a : R ⧸ N₀) = 1
    rw [← hla]
    exact (QuotientGroup.eq_one_iff l).mpr (hLN ⟨hl, h3⟩)
  have hsurj : Function.Surjective δ := Finite.surjective_of_injective hinj
  have hAcomm : A ≤ commutator (R ⧸ N₀) := by
    intro x hx
    obtain ⟨b, hb⟩ := hsurj ⟨x, hx⟩
    have : ⁅π₀ τ, (b : R ⧸ N₀)⁆ = x := congrArg Subtype.val hb
    rw [← this]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [eq_top_iff]
  intro x _
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective x
  have hr : r ∈ ⨆ g : R, conjSubgroup g L := hgen ▸ Subgroup.mem_top r
  refine Subgroup.iSup_induction (fun g : R => conjSubgroup g L)
    (C := fun r => (QuotientGroup.mk r : R ⧸ N₀) ∈ commutator (R ⧸ N₀)) hr ?_ ?_ ?_
  · intro g y hy
    have hl : g⁻¹ * y * g ∈ L := mem_conjSubgroup.mp hy
    have hy' : (QuotientGroup.mk y : R ⧸ N₀) =
        (QuotientGroup.mk g) * (QuotientGroup.mk (g⁻¹ * y * g)) * (QuotientGroup.mk g)⁻¹ := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      group
    rw [hy']
    exact (Subgroup.Normal.conj_mem inferInstance _ (hAcomm ⟨_, hl, rfl⟩) _)
  · exact (QuotientGroup.mk_one N₀ : (QuotientGroup.mk 1 : R ⧸ N₀) = 1) ▸ Subgroup.one_mem _
  · intro a b ha hb
    rw [QuotientGroup.mk_mul]
    exact Subgroup.mul_mem _ ha hb

theorem normalizer_map_of_normalizer [Finite R] (N N₀ L : Subgroup R) [N₀.Normal]
    (hN₀N : N₀ ≤ N)
    (hnorm : ∀ r : R, r ∈ Subgroup.normalizer ((L ⊔ N : Subgroup R) : Set R) →
      r ∈ Subgroup.normalizer (L : Set R)) :
    ∀ e ∈ Subgroup.normalizer (((L.map (QuotientGroup.mk' N₀) ⊔ N.map (QuotientGroup.mk' N₀) :
        Subgroup (R ⧸ N₀)) : Set (R ⧸ N₀))),
      e ∈ Subgroup.normalizer ((L.map (QuotientGroup.mk' N₀) : Subgroup (R ⧸ N₀)) :
        Set (R ⧸ N₀)) := by
  set π₀ := QuotientGroup.mk' N₀ with hπ₀
  intro e he
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective e
  have hker : N₀ ≤ L ⊔ N := hN₀N.trans le_sup_right
  rw [← Subgroup.map_sup] at he
  have hr : r ∈ Subgroup.normalizer ((L ⊔ N : Subgroup R) : Set R) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp he (π₀ x)).mp ⟨x, hx, rfl⟩
    have h2 : π₀ (r * x * r⁻¹) ∈ (L ⊔ N).map π₀ := by
      simpa [hπ₀] using h1
    have h3 : r * x * r⁻¹ ∈ ((L ⊔ N).map π₀).comap π₀ := h2
    rwa [Subgroup.comap_map_eq, (QuotientGroup.ker_mk' N₀), sup_eq_left.mpr hker] at h3
  have hrL := hnorm r hr
  refine Subgroup.mem_normalizer_fintype fun a ha => ?_
  obtain ⟨l, hl, rfl⟩ := ha
  exact ⟨r * l * r⁻¹, (Subgroup.mem_normalizer_iff.mp hrL l).mp hl, by simp [hπ₀]⟩

theorem card_map_eq_of_ker {H₁ H₂ : Type*} [Group H₁] [Group H₂] (L : Subgroup R)
    (f : R →* H₁) (g : R →* H₂) (h : ∀ x ∈ L, f x = 1 ↔ g x = 1) :
    Nat.card (L.map f) = Nat.card (L.map g) := by
  have hf : L.map f = (f.comp L.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hg : L.map g = (g.comp L.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hk : (f.comp L.subtype).ker = (g.comp L.subtype).ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact h x x.2
  rw [hf, hg, ← Subgroup.index_ker, ← Subgroup.index_ker, hk]

theorem exists_cover_data [Finite R] (N N₀ L : Subgroup R) [N₀.Normal]
    (hN₀N : N₀ ≤ N) (hgen : ⨆ g : R, conjSubgroup g L = ⊤)
    (hcomm : ∀ (g : R), ∀ n ∈ N, ∀ l ∈ conjSubgroup g L, ⁅n, l⁆ ∈ N₀) (hLN : L ⊓ N ≤ N₀)
    (hab : ∀ l ∈ L, ∀ l' ∈ L, ⁅l, l'⁆ ∈ N ∧ l ^ 2 ∈ N) {τ : R}
    (hτL : τ ∈ Subgroup.normalizer (L : Set R)) (hτ : ∀ l ∈ L, ⁅τ, l⁆ ∈ N → l ∈ N)
    (hnorm : ∀ r : R, r ∈ Subgroup.normalizer ((L ⊔ N : Subgroup R) : Set R) →
      r ∈ Subgroup.normalizer (L : Set R)) :
    commutator (R ⧸ N₀) = ⊤ ∧
      N.map (QuotientGroup.mk' N₀) ≤ Subgroup.center (R ⧸ N₀) ∧
      L.map (QuotientGroup.mk' N₀) ⊓ N.map (QuotientGroup.mk' N₀) = ⊥ ∧
      IsElemAbelian 2 (L.map (QuotientGroup.mk' N₀)) ∧
      (∀ e ∈ Subgroup.normalizer (((L.map (QuotientGroup.mk' N₀) ⊔
          N.map (QuotientGroup.mk' N₀) : Subgroup (R ⧸ N₀)) : Set (R ⧸ N₀))),
        e ∈ Subgroup.normalizer ((L.map (QuotientGroup.mk' N₀) : Subgroup (R ⧸ N₀)) :
          Set (R ⧸ N₀))) := by
  refine ⟨commutator_eq_top_of_root N N₀ L hN₀N hgen hLN hab hτL hτ,
    map_le_center_of_comm N N₀ L hgen hcomm, ?_,
    isElemAbelian_map_of_ab N N₀ L hLN hN₀N hab, normalizer_map_of_normalizer N N₀ L hN₀N hnorm⟩
  rw [eq_bot_iff]
  rintro x ⟨⟨l, hl, rfl⟩, ⟨n, hn, hnl⟩⟩
  have h1 : l⁻¹ * n ∈ N₀ := by
    have h1 : (QuotientGroup.mk' N₀) n = (QuotientGroup.mk' N₀) l := hnl
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    have := N₀.inv_mem h1
    simpa using this
  have hlN : l ∈ N := by
    have : l = n * (l⁻¹ * n)⁻¹ := by group
    rw [this]
    exact N.mul_mem hn (N.inv_mem (hN₀N h1))
  show (QuotientGroup.mk' N₀) l = 1
  rw [QuotientGroup.mk'_apply]
  exact (QuotientGroup.eq_one_iff l).mpr (hLN ⟨hl, hlN⟩)

end CFSG.RankThree.GF2n.Stroth80
