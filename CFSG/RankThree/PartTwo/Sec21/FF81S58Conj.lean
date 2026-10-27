module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.FF81Sec42Q
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S58

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}

private theorem s58_zp (g b : G) :
    conjBy g (Subgroup.zpowers b) = Subgroup.zpowers (g * b * g⁻¹) :=
  MonoidHom.map_zpowers _ _

private theorem s58_conjBy_inf (g : G) (U V : Subgroup G) :
    conjBy g (U ⊓ V) = conjBy g U ⊓ conjBy g V :=
  Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective

private theorem s58_conjBy_closure3 (g a c d : G) :
    conjBy g (Subgroup.closure ({a, c, d} : Set G)) =
      Subgroup.closure {g * a * g⁻¹, g * c * g⁻¹, g * d * g⁻¹} := by
  rw [conjBy, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_singleton]
  rfl

private theorem s58_conjBy_closure4 (g a c d e : G) :
    conjBy g (Subgroup.closure ({a, c, d, e} : Set G)) =
      Subgroup.closure {g * a * g⁻¹, g * c * g⁻¹, g * d * g⁻¹, g * e * g⁻¹} := by
  rw [conjBy, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_insert_eq, Set.image_singleton]
  rfl

private theorem s58_conj_cancel (g : G) (H : Subgroup G) :
    conjBy g (conjBy g⁻¹ H) = H := by
  have h := FF79.L14.conjBy_conjBy_inv g⁻¹ H
  rwa [inv_inv] at h

private theorem s58_conj_fn (x n : G) (H : Subgroup G) :
    conjBy (x * n * x⁻¹) H = conjBy x (conjBy n (conjBy x⁻¹ H)) := by
  simp only [FF79.L41.conjBy_conjBy, mul_assoc]

private theorem s58_conj_fn' (x n : G) (H : Subgroup G) :
    conjBy (x⁻¹ * n * x) H = conjBy x⁻¹ (conjBy n (conjBy x H)) := by
  simp only [FF79.L41.conjBy_conjBy, mul_assoc]

private theorem s58_conj_inv_eq (x a : G) : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by
  group

private theorem s58_mem_six {x z c₁ c₂ c₃ : G}
    (h : z ∈ ({c₁, c₁⁻¹, c₂, c₂⁻¹, c₃, c₃⁻¹} : Set G)) :
    x * z * x⁻¹ ∈ ({x * c₁ * x⁻¹, (x * c₁ * x⁻¹)⁻¹, x * c₂ * x⁻¹, (x * c₂ * x⁻¹)⁻¹,
      x * c₃ * x⁻¹, (x * c₃ * x⁻¹)⁻¹} : Set G) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (by group))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by group))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by group)))))

private theorem s58_isElemAb_conjBy {p k : ℕ} {H : Subgroup G} (h : IsElemAb p k H) (g : G) :
    IsElemAb p k (conjBy g H) :=
  ⟨CFSG.IsElementaryAbelian.subgroup_map h.1 (MulAut.conj g).toMonoidHom,
    by rw [card_conjBy]; exact h.2⟩

theorem FF81Basis.conj (hB : FF81Basis b L B b₁ b₂ b₃) {x : G} (hx : x ∈ L) :
    FF81Basis b L (conjBy x B) (x * b₁ * x⁻¹) (x * b₂ * x⁻¹) (x * b₃ * x⁻¹) := by
  have hcomm : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC hx)
  have hxb : x * b * x⁻¹ = b := by rw [hcomm, mul_inv_cancel_right]
  have hxb' : x⁻¹ * b * x = b := by rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
  have hxbi : x * b⁻¹ * x⁻¹ = b⁻¹ := by rw [s58_conj_inv_eq, hxb]
  have hxZ : conjBy x (Subgroup.zpowers b) = Subgroup.zpowers b := by
    rw [s58_zp, hxb]
  have hxiZ : conjBy x⁻¹ (Subgroup.zpowers b) = Subgroup.zpowers b := by
    rw [s58_zp, inv_inv, hxb']
  have hxnx : ∀ n ∈ L, x * n * x⁻¹ ∈ L := fun n hn =>
    L.mul_mem (L.mul_mem hx hn) (L.inv_mem hx)
  have key : ∀ n a c : G, n * a * n⁻¹ = c →
      (x * n * x⁻¹) * (x * a * x⁻¹) * (x * n * x⁻¹)⁻¹ = x * c * x⁻¹ := by
    intro n a c h
    subst h
    group
  have key' : ∀ n c : G, n * b * n⁻¹ = c →
      (x * n * x⁻¹) * b * (x * n * x⁻¹)⁻¹ = x * c * x⁻¹ := by
    intro n c h
    subst h
    calc (x * n * x⁻¹) * b * (x * n * x⁻¹)⁻¹ = x * (n * (x⁻¹ * b * x) * n⁻¹) * x⁻¹ := by
          group
      _ = x * (n * b * n⁻¹) * x⁻¹ := by rw [hxb']
  have hNn : ∀ n ∈ Nor B, x * n * x⁻¹ ∈ Nor (conjBy x B) := by
    intro n hn
    rw [Q42.nor_conjBy, mem_conjBy_iff]
    have e : x⁻¹ * (x * n * x⁻¹) * x = n := by group
    rw [e]
    exact hn
  have hclos : conjBy x (Subgroup.closure ({b₁, b₂, b₃} : Set G)) =
      Subgroup.closure {x * b₁ * x⁻¹, x * b₂ * x⁻¹, x * b₃ * x⁻¹} :=
    s58_conjBy_closure3 x b₁ b₂ b₃
  have hxL : conjBy x L = L := by
    ext y
    rw [mem_conjBy_iff]
    constructor
    · intro h
      have h2 := L.mul_mem (L.mul_mem hx h) (L.inv_mem hx)
      rwa [show x * (x⁻¹ * y * x) * x⁻¹ = y by group] at h2
    · intro h
      exact L.mul_mem (L.mul_mem (L.inv_mem hx) h) hx
  have hBx : conjBy x B = Subgroup.closure {b, x * b₁ * x⁻¹, x * b₂ * x⁻¹, x * b₃ * x⁻¹} := by
    rw [hB.mono.2.1, s58_conjBy_closure4, hxb]
  have hy₁ : x * b₁ * x⁻¹ ∈ L := hxnx b₁ hB.hb₁
  have hy₂ : x * b₂ * x⁻¹ ∈ L := hxnx b₂ hB.hb₂
  have hy₃ : x * b₃ * x⁻¹ ∈ L := hxnx b₃ hB.hb₃
  have helem : IsElemAb 3 3 (Subgroup.closure {x * b₁ * x⁻¹, x * b₂ * x⁻¹, x * b₃ * x⁻¹}) := by
    rw [← hclos]
    exact s58_isElemAb_conjBy hB.elem x
  have hselfcen : L ⊓ CenS (Subgroup.closure {x * b₁ * x⁻¹, x * b₂ * x⁻¹, x * b₃ * x⁻¹}) =
      Subgroup.closure {x * b₁ * x⁻¹, x * b₂ * x⁻¹, x * b₃ * x⁻¹} := by
    have hc : L ⊓ CenS (conjBy x (Subgroup.closure ({b₁, b₂, b₃} : Set G))) =
        conjBy x (L ⊓ CenS (Subgroup.closure ({b₁, b₂, b₃} : Set G))) := by
      rw [s58_conjBy_inf, hxL, FF79.conjBy_cenS]
    rw [← hclos, hc, hB.selfcen]
  have hmono : HasH0 (conjBy x B) b (x * b₁ * x⁻¹) (x * b₂ * x⁻¹) (x * b₃ * x⁻¹) := by
    obtain ⟨hel, _, ⟨n₀, hn₀, a0, a1, a2, a3⟩, ⟨n₁, hn₁, c0, c1, c2, c3⟩,
      ⟨n₂, hn₂, d0, d1, d2, d3⟩, ⟨n₃, hn₃, e0, e1, e2, e3⟩⟩ := hB.mono
    exact ⟨s58_isElemAb_conjBy hel x, hBx,
      ⟨x * n₀ * x⁻¹, hNn n₀ hn₀, by rw [key' _ _ a0, hxbi], key _ _ _ a1, key _ _ _ a2,
        key _ _ _ a3⟩,
      ⟨x * n₁ * x⁻¹, hNn n₁ hn₁, by rw [key' _ _ c0, hxb], by rw [key _ _ _ c1, s58_conj_inv_eq],
        key _ _ _ c2, key _ _ _ c3⟩,
      ⟨x * n₂ * x⁻¹, hNn n₂ hn₂, by rw [key' _ _ d0, hxb], key _ _ _ d1, key _ _ _ d2,
        key _ _ _ d3⟩,
      ⟨x * n₃ * x⁻¹, hNn n₃ hn₃, by rw [key' _ _ e0, hxb], key _ _ _ e1, key _ _ _ e2,
        key _ _ _ e3⟩⟩
  have hmonoL : ∃ n ∈ L, n * (x * b₁ * x⁻¹) * n⁻¹ = x * b₁ * x⁻¹ ∧
      n * (x * b₂ * x⁻¹) * n⁻¹ = x * b₃ * x⁻¹ ∧ n * (x * b₃ * x⁻¹) * n⁻¹ = x * b₂ * x⁻¹ := by
    obtain ⟨n, hn, c1, c2, c3⟩ := hB.monoL
    exact ⟨x * n * x⁻¹, hxnx n hn, key _ _ _ c1, key _ _ _ c2, key _ _ _ c3⟩
  have hfus : ∀ D ∈ ConjLines (conjBy x B) b,
      ∃ n ∈ Nor (conjBy x B), conjBy n (Subgroup.zpowers b) = D := by
    intro D hD
    obtain ⟨hDle, g, rfl⟩ := hD
    have hle : conjBy x⁻¹ (conjBy g (Subgroup.zpowers b)) ≤ B := by
      calc conjBy x⁻¹ (conjBy g (Subgroup.zpowers b)) ≤ conjBy x⁻¹ (conjBy x B) :=
            Subgroup.map_mono hDle
        _ = B := FF79.L14.conjBy_conjBy_inv x B
    obtain ⟨n, hn, hnD⟩ := hB.fus (conjBy x⁻¹ (conjBy g (Subgroup.zpowers b)))
      ⟨hle, x⁻¹ * g, (FF79.L41.conjBy_conjBy x⁻¹ g _).symm⟩
    refine ⟨x * n * x⁻¹, hNn n hn, ?_⟩
    rw [s58_conj_fn, hxiZ, hnD, s58_conj_cancel]
  have hstab : ∀ n ∈ Nor (conjBy x B), conjBy n (Subgroup.zpowers b) = Subgroup.zpowers b →
      n * b * n⁻¹ ∈ ({b, b⁻¹} : Set G) ∧
        ∀ y ∈ ({x * b₁ * x⁻¹, x * b₂ * x⁻¹, x * b₃ * x⁻¹} : Set G),
          n * y * n⁻¹ ∈ ({x * b₁ * x⁻¹, (x * b₁ * x⁻¹)⁻¹, x * b₂ * x⁻¹, (x * b₂ * x⁻¹)⁻¹,
            x * b₃ * x⁻¹, (x * b₃ * x⁻¹)⁻¹} : Set G) := by
    intro n hn hnZ
    rw [Q42.nor_conjBy, mem_conjBy_iff] at hn
    have hmZ : conjBy (x⁻¹ * n * x) (Subgroup.zpowers b) = Subgroup.zpowers b := by
      rw [s58_conj_fn', hxZ, hnZ, hxiZ]
    obtain ⟨h1, h2⟩ := hB.stab (x⁻¹ * n * x) hn hmZ
    have hnm : ∀ a : G,
        n * (x * a * x⁻¹) * n⁻¹ = x * ((x⁻¹ * n * x) * a * (x⁻¹ * n * x)⁻¹) * x⁻¹ := by
      intro a
      group
    refine ⟨?_, ?_⟩
    · have e : n * b * n⁻¹ = x * ((x⁻¹ * n * x) * b * (x⁻¹ * n * x)⁻¹) * x⁻¹ := by
        calc n * b * n⁻¹ = n * (x * b * x⁻¹) * n⁻¹ := by rw [hxb]
          _ = _ := hnm b
      rw [e]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢
      rcases h1 with h1 | h1
      · left
        rw [h1, hxb]
      · right
        rw [h1, s58_conj_inv_eq, hxb]
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · rw [hnm b₁]
        exact s58_mem_six (h2 b₁ (by simp))
      · rw [hnm b₂]
        exact s58_mem_six (h2 b₂ (by simp))
      · rw [hnm b₃]
        exact s58_mem_six (h2 b₃ (by simp))
  have hcenSyl : ∀ y ∈ CenS (conjBy x B), IsPGroup 3 (Subgroup.zpowers y) →
      y ∈ conjBy x B := by
    intro y hy hyP
    rw [FF79.conjBy_cenS, mem_conjBy_iff] at hy
    have hz : Subgroup.zpowers (x⁻¹ * y * x) = conjBy x⁻¹ (Subgroup.zpowers y) := by
      rw [s58_zp, inv_inv]
    have hzP : IsPGroup 3 (Subgroup.zpowers (x⁻¹ * y * x)) := by
      rw [hz]
      exact FF79.isPGroup_conjBy hyP x⁻¹
    rw [mem_conjBy_iff]
    exact hB.cenSyl _ hy hzP
  have hcenOdd : Odd (Nat.card (CenS (conjBy x B))) := by
    rw [FF79.conjBy_cenS, card_conjBy]
    exact hB.cenOdd
  have hmeet : ∃ n ∈ Nor (conjBy x B),
      n * b * n⁻¹ ∈ Subgroup.closure {x * b₁ * x⁻¹, x * b₂ * x⁻¹, x * b₃ * x⁻¹} := by
    obtain ⟨n, hn, hnb⟩ := hB.meet
    refine ⟨x * n * x⁻¹, hNn n hn, ?_⟩
    rw [key' n _ rfl, ← hclos, mem_conjBy_iff]
    have e : x⁻¹ * (x * (n * b * n⁻¹) * x⁻¹) * x = n * b * n⁻¹ := by group
    rw [e]
    exact hnb
  exact
    { hyp := hB.hyp
      hb₁ := hy₁
      hb₂ := hy₂
      hb₃ := hy₃
      elem := helem
      selfcen := hselfcen
      mono := hmono
      monoL := hmonoL
      fus := hfus
      stab := hstab
      cenSyl := hcenSyl
      o3odd := hB.o3odd
      rank3 := hB.rank3
      cenOdd := hcenOdd
      meet := hmeet }

end CFSG.RankThree.PartTwo.Sec21.FF81.S58
