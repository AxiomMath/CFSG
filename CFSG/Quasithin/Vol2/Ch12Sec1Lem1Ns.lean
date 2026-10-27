module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1Pair
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem6Lv

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut slGraphAut_matrix)
open scoped Matrix

namespace Sec1211Ns

variable {G : Type} [Group G]

structure Setting [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ) (a₀ c₀ : G) extends
    KGH91.Setting G T L V V₁ V₂ n where
  hTL : T ≤ Subgroup.normalizer (L : Set G)
  ha₀ : a₀ ∈ V₁
  hc₀ : c₀ ∈ V₂
  hns : KGH91.pairing C₁ C₂ a₀ c₀ = 1

namespace Setting

@[expose] def W₁ [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
    (S : Setting T L V V₁ V₂ n a₀ c₀) : Subgroup G where
  carrier := {a | a ∈ V₁ ∧ KGH91.pairing S.C₁ S.C₂ a c₀ = 0}
  mul_mem' {a b} ha hb := ⟨V₁.mul_mem ha.1 hb.1, by
    rw [(KGH91.isDualPairing S.C₁ S.C₂ S.dual).1 a ha.1 b hb.1 c₀ S.hc₀, ha.2, hb.2, add_zero]⟩
  one_mem' := ⟨V₁.one_mem, by simp [KGH91.pairing, S.C₁.E_one]⟩
  inv_mem' {a} ha := by
    have hV := Sec121Thm.isElemAbelian_of_isPrimeReduced S.hyp.le S.hyp.reduced
    have ha2 : a⁻¹ = a := by
      have h := hV.2 a (S.le₁ ha.1)
      rw [pow_two] at h
      exact inv_eq_of_mul_eq_one_right h
    show a⁻¹ ∈ V₁ ∧ _
    rw [ha2]
    exact ha

@[expose] def W₂ [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
    (S : Setting T L V V₁ V₂ n a₀ c₀) : Subgroup G where
  carrier := {c | c ∈ V₂ ∧ KGH91.pairing S.C₁ S.C₂ a₀ c = 0}
  mul_mem' {c d} hc hd := ⟨V₂.mul_mem hc.1 hd.1, by
    rw [(KGH91.isDualPairing S.C₁ S.C₂ S.dual).2.1 a₀ S.ha₀ c hc.1 d hd.1, hc.2, hd.2,
      add_zero]⟩
  one_mem' := ⟨V₂.one_mem, by simp [KGH91.pairing, S.C₂.E_one]⟩
  inv_mem' {c} hc := by
    have hV := Sec121Thm.isElemAbelian_of_isPrimeReduced S.hyp.le S.hyp.reduced
    have hc2 : c⁻¹ = c := by
      have h := hV.2 c (S.le₂ hc.1)
      rw [pow_two] at h
      exact inv_eq_of_mul_eq_one_right h
    show c⁻¹ ∈ V₂ ∧ _
    rw [hc2]
    exact hc

variable [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
  (S : Setting T L V V₁ V₂ n a₀ c₀)
include S

theorem hVe : IsElemAbelian 2 V := Sec121Thm.isElemAbelian_of_isPrimeReduced S.hyp.le S.hyp.reduced

theorem inv_eq {x : G} (hx : x ∈ V) : x⁻¹ = x := by
  have h := S.hVe.2 x hx
  rw [pow_two] at h
  exact inv_eq_of_mul_eq_one_right h

theorem one_add : 1 + (n - 1) = n := by rcases S.hyp.rank with h | h <;> omega

theorem three_le : 3 ≤ n - 1 := by rcases S.hyp.rank with h | h <;> omega

theorem three_le' : 3 ≤ n := by rcases S.hyp.rank with h | h <;> omega

theorem hxy : S.C₂.E c₀ ⬝ᵥ S.C₁.E a₀ = 1 := by
  rw [dotProduct_comm]
  exact S.hns

theorem v_mem : a₀ * c₀ ∈ V := V.mul_mem (S.le₁ S.ha₀) (S.le₂ S.hc₀)

theorem a₀_ne : a₀ ≠ 1 := by
  rintro rfl
  have h := S.hns
  simp [KGH91.pairing, S.C₁.E_one] at h

theorem c₀_ne : c₀ ≠ 1 := by
  rintro rfl
  have h := S.hns
  simp [KGH91.pairing, S.C₂.E_one] at h

theorem mem_centralizer_iff (l : ↥L) :
    (l : G) ∈ Subgroup.centralizer ({a₀ * c₀} : Set G) ↔
      S.C₁.ρ l ∈ PairStab.pairStab (S.C₁.E a₀) (S.C₂.E c₀) := by
  rw [PairStab.mem_pairStab, ← S.C₁.conj l a₀ S.ha₀, ← S.dual, ← S.C₂.conj l c₀ S.hc₀,
    Subgroup.mem_centralizer_singleton_iff]
  have hfix : (l : G) * (a₀ * c₀) * (l : G)⁻¹ = a₀ * c₀ ↔
      (l : G) * a₀ * (l : G)⁻¹ = a₀ ∧ (l : G) * c₀ * (l : G)⁻¹ = c₀ := by
    have e : (l : G) * (a₀ * c₀) * (l : G)⁻¹ =
        ((l : G) * a₀ * (l : G)⁻¹) * ((l : G) * c₀ * (l : G)⁻¹) := by group
    rw [e]
    constructor
    · intro h
      exact S.decomp_unique (S.C₁.conj_mem l S.ha₀) S.ha₀ (S.C₂.conj_mem l S.hc₀) S.hc₀ h
    · rintro ⟨h₁, h₂⟩
      rw [h₁, h₂]
  constructor
  · intro h
    have h' : (l : G) * (a₀ * c₀) * (l : G)⁻¹ = a₀ * c₀ := by rw [h, mul_inv_cancel_right]
    obtain ⟨h₁, h₂⟩ := hfix.mp h'
    exact ⟨by rw [h₁], by rw [h₂]⟩
  · rintro ⟨h₁, h₂⟩
    have h₁' := S.C₁.inj _ (S.C₁.conj_mem l S.ha₀) _ S.ha₀ h₁
    have h₂' := S.C₂.inj _ (S.C₂.conj_mem l S.hc₀) _ S.hc₀ h₂
    have h' := hfix.mpr ⟨h₁', h₂'⟩
    calc (l : G) * (a₀ * c₀) = ((l : G) * (a₀ * c₀) * (l : G)⁻¹) * l := by group
      _ = a₀ * c₀ * l := by rw [h']

theorem map_inf : ((L ⊓ Subgroup.centralizer ({a₀ * c₀} : Set G)).subgroupOf L).map S.C₁.ρ =
    PairStab.pairStab (S.C₁.E a₀) (S.C₂.E c₀) := by
  ext g
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact (S.mem_centralizer_iff l).mp (Subgroup.mem_subgroupOf.mp hl).2
  · intro hg
    obtain ⟨l, rfl⟩ := S.C₁.ρ_surj g
    exact ⟨l, Subgroup.mem_subgroupOf.mpr ⟨l.2, (S.mem_centralizer_iff l).mpr hg⟩, rfl⟩

theorem exists_mem_lv {g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)}
    (hg : g ∈ PairStab.pairStab (S.C₁.E a₀) (S.C₂.E c₀)) :
    ∃ l : ↥L, (l : G) ∈ Sec1216Lv.lv L (a₀ * c₀) ∧ S.C₁.ρ l = g := by
  have h1 : (perfectCore ((L ⊓ Subgroup.centralizer ({a₀ * c₀} : Set G)).subgroupOf L)).map
      S.C₁.ρ = PairStab.pairStab (S.C₁.E a₀) (S.C₂.E c₀) := by
    rw [map_perfectCore, S.map_inf, perfectCore_eq_self_of_perfect
      (PairStab.commutator_eq S.one_add S.three_le S.hxy)]
  have h2 : (perfectCore ((L ⊓ Subgroup.centralizer ({a₀ * c₀} : Set G)).subgroupOf L)).map
      L.subtype = Sec1216Lv.lv L (a₀ * c₀) := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    rfl
  rw [← h1] at hg
  obtain ⟨l, hl, rfl⟩ := hg
  exact ⟨l, h2 ▸ ⟨l, hl, rfl⟩, rfl⟩

theorem lv_fix {l : G} (hl : l ∈ Sec1216Lv.lv L (a₀ * c₀)) :
    l * a₀ * l⁻¹ = a₀ ∧ l * c₀ * l⁻¹ = c₀ := by
  have hlv := Subgroup.mem_centralizer_singleton_iff.mp (Sec1216Lv.lv_le_centralizer L _ hl)
  have e : l * a₀ * l⁻¹ * (l * c₀ * l⁻¹) = a₀ * c₀ := by
    calc l * a₀ * l⁻¹ * (l * c₀ * l⁻¹) = l * (a₀ * c₀) * l⁻¹ := by group
      _ = a₀ * c₀ := by rw [hlv, mul_inv_cancel_right]
  have hlN := Subgroup.le_normalizer (Sec1216Lv.lv_le_L L _ hl)
  exact S.decomp_unique (S.C₁.conj_mem ⟨l, Sec1216Lv.lv_le_L L _ hl⟩ S.ha₀) S.ha₀
    (S.C₂.conj_mem ⟨l, Sec1216Lv.lv_le_L L _ hl⟩ S.hc₀) S.hc₀ e

theorem V_le_normalizer_lv : V ≤ Subgroup.normalizer (Sec1216Lv.lv L (a₀ * c₀) : Set G) := by
  refine Sec1216Lv.le_normalizer_lv S.hyp.le fun x hx => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact S.comm hx S.v_mem

theorem mul_conj_mem {b l : G} (hb : b ∈ V) (hl : l ∈ Sec1216Lv.lv L (a₀ * c₀)) :
    b * (l * b * l⁻¹) ∈ Sec1216Lv.lv L (a₀ * c₀) := by
  have e : b * (l * b * l⁻¹) = b * l * b⁻¹ * l⁻¹ := by
    rw [S.inv_eq hb]
    group
  rw [e]
  exact (Sec1216Lv.lv L _).mul_mem
    ((Subgroup.mem_normalizer_iff.mp (S.V_le_normalizer_lv hb) l).mp hl)
    ((Sec1216Lv.lv L _).inv_mem hl)

theorem mem_W₁ {a : G} : a ∈ S.W₁ ↔ a ∈ V₁ ∧ S.C₁.E a ⬝ᵥ S.C₂.E c₀ = 0 := Iff.rfl

theorem mem_W₂ {c : G} : c ∈ S.W₂ ↔ c ∈ V₂ ∧ S.C₁.E a₀ ⬝ᵥ S.C₂.E c = 0 := Iff.rfl

theorem W₁_le : S.W₁ ≤ V₁ := fun _ h => h.1

theorem W₂_le : S.W₂ ≤ V₂ := fun _ h => h.1

theorem inv_mem_W₁ {x : Fin n → ZMod 2} (hx : x ⬝ᵥ S.C₂.E c₀ = 0) : S.C₁.inv x ∈ S.W₁ :=
  ⟨S.C₁.inv_mem x, by show S.C₁.E (S.C₁.inv x) ⬝ᵥ S.C₂.E c₀ = 0; rw [S.C₁.E_inv]; exact hx⟩

theorem inv_mem_W₂ {y : Fin n → ZMod 2} (hy : S.C₁.E a₀ ⬝ᵥ y = 0) : S.C₂.inv y ∈ S.W₂ :=
  ⟨S.C₂.inv_mem y, by show S.C₁.E a₀ ⬝ᵥ S.C₂.E (S.C₂.inv y) = 0; rw [S.C₂.E_inv]; exact hy⟩

theorem y₀_ne : S.C₂.E c₀ ≠ 0 := fun h => S.c₀_ne (S.C₂.eq_one_of_E S.hc₀ h)

theorem x₀_ne : S.C₁.E a₀ ≠ 0 := fun h => S.a₀_ne (S.C₁.eq_one_of_E S.ha₀ h)

theorem exists_commutator₁ {a : G} (ha : a ∈ S.W₁) :
    ∃ b ∈ S.W₁, ∃ l ∈ Sec1216Lv.lv L (a₀ * c₀), a = b * (l * b * l⁻¹) := by
  obtain ⟨x, hx, hx0, hxa⟩ := VecStab.exists_perp_ne S.three_le' S.y₀_ne (S.C₁.E a)
  have hx' : x ⬝ᵥ S.C₂.E c₀ = 0 := by rw [dotProduct_comm]; exact hx
  have hxa' : (x + S.C₁.E a) ⬝ᵥ S.C₂.E c₀ = 0 := by
    rw [add_dotProduct, hx', (S.mem_W₁).mp ha |>.2, add_zero]
  obtain ⟨g, hg, hgx⟩ := PairStab.exists_mulVec S.one_add (by have := S.three_le; omega) S.hxy
    hx' hxa' hx0 (fun h => hxa (VecStab.eq_of_add_eq_zero h))
  obtain ⟨l, hl, hlg⟩ := S.exists_mem_lv hg
  have hb := S.inv_mem_W₁ hx'
  refine ⟨S.C₁.inv x, hb, l, hl, ?_⟩
  apply S.C₁.inj a ((S.mem_W₁).mp ha).1 _ (V₁.mul_mem hb.1 (S.C₁.conj_mem l hb.1))
  rw [S.C₁.map_mul _ hb.1 _ (S.C₁.conj_mem l hb.1), S.C₁.conj l _ hb.1, hlg, S.C₁.E_inv, hgx,
    ← add_assoc, VecStab.add_self, zero_add]

theorem exists_commutator₂ {c : G} (hc : c ∈ S.W₂) :
    ∃ d ∈ S.W₂, ∃ l ∈ Sec1216Lv.lv L (a₀ * c₀), c = d * (l * d * l⁻¹) := by
  obtain ⟨y, hy, hy0, hyc⟩ := VecStab.exists_perp_ne S.three_le' S.x₀_ne (S.C₂.E c)
  have hy' : y ⬝ᵥ S.C₁.E a₀ = 0 := by rw [dotProduct_comm]; exact hy
  have hyc' : (y + S.C₂.E c) ⬝ᵥ S.C₁.E a₀ = 0 := by
    rw [add_dotProduct, hy', dotProduct_comm, (S.mem_W₂).mp hc |>.2, add_zero]
  obtain ⟨g, hg, hgy⟩ := PairStab.exists_dual S.one_add (by have := S.three_le; omega) S.hxy
    hy' hyc' hy0 (fun h => hyc (VecStab.eq_of_add_eq_zero h))
  obtain ⟨l, hl, hlg⟩ := S.exists_mem_lv hg
  have hd := S.inv_mem_W₂ hy
  refine ⟨S.C₂.inv y, hd, l, hl, ?_⟩
  apply S.C₂.inj c ((S.mem_W₂).mp hc).1 _ (V₂.mul_mem hd.1 (S.C₂.conj_mem l hd.1))
  rw [S.C₂.map_mul _ hd.1 _ (S.C₂.conj_mem l hd.1), S.C₂.conj l _ hd.1, S.dual, hlg, S.C₂.E_inv,
    hgy, ← add_assoc, VecStab.add_self, zero_add]

theorem W₁_le_lv : S.W₁ ≤ Sec1216Lv.lv L (a₀ * c₀) := by
  intro a ha
  obtain ⟨b, hb, l, hl, rfl⟩ := S.exists_commutator₁ ha
  exact S.mul_conj_mem (S.le₁ hb.1) hl

theorem W₂_le_lv : S.W₂ ≤ Sec1216Lv.lv L (a₀ * c₀) := by
  intro c hc
  obtain ⟨d, hd, l, hl, rfl⟩ := S.exists_commutator₂ hc
  exact S.mul_conj_mem (S.le₂ hd.1) hl

theorem lv_conj_mem_W₁ {l a : G} (hl : l ∈ Sec1216Lv.lv L (a₀ * c₀)) (ha : a ∈ S.W₁) :
    l * a * l⁻¹ ∈ S.W₁ := by
  have hlL := Sec1216Lv.lv_le_L L _ hl
  have hlN := Subgroup.le_normalizer hlL
  have h1 := S.pairing_conj hlN (S.hyp.norm₁ hlL) (S.hyp.norm₂ hlL) a ha.1 c₀ S.hc₀
  rw [(S.lv_fix hl).2] at h1
  exact ⟨(Subgroup.mem_normalizer_iff.mp (S.hyp.norm₁ hlL) a).mp ha.1, by rw [h1]; exact ha.2⟩

theorem lv_conj_mem_W₂ {l c : G} (hl : l ∈ Sec1216Lv.lv L (a₀ * c₀)) (hc : c ∈ S.W₂) :
    l * c * l⁻¹ ∈ S.W₂ := by
  have hlL := Sec1216Lv.lv_le_L L _ hl
  have hlN := Subgroup.le_normalizer hlL
  have h1 := S.pairing_conj hlN (S.hyp.norm₁ hlL) (S.hyp.norm₂ hlL) a₀ S.ha₀ c hc.1
  rw [(S.lv_fix hl).1] at h1
  exact ⟨(Subgroup.mem_normalizer_iff.mp (S.hyp.norm₂ hlL) c).mp hc.1, by rw [h1]; exact hc.2⟩

theorem eq_one_of_fixed₁ {a : G} (ha : a ∈ S.W₁)
    (h : ∀ l ∈ Sec1216Lv.lv L (a₀ * c₀), l * a * l⁻¹ = a) : a = 1 := by
  by_contra ha1
  have hE0 : S.C₁.E a ≠ 0 := fun h0 => ha1 (S.C₁.eq_one_of_E ha.1 h0)
  obtain ⟨x, hx, hx0, hxa⟩ := VecStab.exists_perp_ne S.three_le' S.y₀_ne (S.C₁.E a)
  have hx' : x ⬝ᵥ S.C₂.E c₀ = 0 := by rw [dotProduct_comm]; exact hx
  obtain ⟨g, hg, hga⟩ := PairStab.exists_mulVec S.one_add (by have := S.three_le; omega) S.hxy
    ((S.mem_W₁).mp ha).2 hx' hE0 hx0
  obtain ⟨l, hl, hlg⟩ := S.exists_mem_lv hg
  have h1 := congrArg S.C₁.E (h l hl)
  rw [S.C₁.conj l a ha.1, hlg, hga] at h1
  exact hxa h1

theorem eq_one_of_fixed₂ {c : G} (hc : c ∈ S.W₂)
    (h : ∀ l ∈ Sec1216Lv.lv L (a₀ * c₀), l * c * l⁻¹ = c) : c = 1 := by
  by_contra hc1
  have hE0 : S.C₂.E c ≠ 0 := fun h0 => hc1 (S.C₂.eq_one_of_E hc.1 h0)
  obtain ⟨y, hy, hy0, hyc⟩ := VecStab.exists_perp_ne S.three_le' S.x₀_ne (S.C₂.E c)
  have hy' : y ⬝ᵥ S.C₁.E a₀ = 0 := by rw [dotProduct_comm]; exact hy
  have hc' : S.C₂.E c ⬝ᵥ S.C₁.E a₀ = 0 := by rw [dotProduct_comm]; exact ((S.mem_W₂).mp hc).2
  obtain ⟨g, hg, hgc⟩ := PairStab.exists_dual S.one_add (by have := S.three_le; omega) S.hxy
    hc' hy' hE0 hy0
  obtain ⟨l, hl, hlg⟩ := S.exists_mem_lv hg
  have h1 := congrArg S.C₂.E (h l hl)
  rw [S.C₂.conj l c hc.1, S.dual, hlg, hgc] at h1
  exact hyc h1

end Setting

end Sec1211Ns

end CFSG.Quasithin.H13
