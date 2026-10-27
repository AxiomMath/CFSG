module

public import CFSG.Quasithin.EmptyFaithful.ModHS24
public import CFSG.Quasithin.EmptyFaithful.ModHM24a
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24

public section

namespace CFSG.Quasithin.ModH.M24b

open CFSG.Quasithin.ModH.S24 CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin.ModG (allL allL_iff ev ev_mem ev_append ev_invW ev_nil ev_cons invW)
open CFSG.Quasithin

theorem dataOK_facts {comp : ℕ → ℕ → ℕ} {kId : ℕ} {gC K : List ℕ} {j z : ℕ}
    (h : dataOK comp kId gC K (buckets K j) j z = true) :
    K.Nodup ∧ kId ∈ K ∧ (∀ k ∈ K, ∀ g ∈ gC, comp k g ∈ K) := by
  simp only [dataOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hnd, h1⟩, hcl⟩, -⟩ := h
  refine ⟨nodup_of_buckets K j hnd, (memBk_iff K j kId).1 h1, fun k hk g hg => ?_⟩
  exact (memBk_iff K j _).1 (allL_iff.1 (allL_iff.1 hcl k hk) g hg)

@[expose] def Sg : Subgroup G := Subgroup.closure {x | x ∈ tg}

theorem Sg_data : tK.Nodup ∧ kIdn 24 ∈ tK ∧ ∀ k ∈ tK, ∀ g ∈ tg, compn 24 k (cd g) ∈ tK := by
  obtain ⟨h1, h2, h3⟩ := dataOK_facts dataOK_true
  refine ⟨h1, h2, fun k hk g hg => h3 k hk (cd g) ?_⟩
  rw [← tg_codes]
  exact List.mem_map_of_mem hg

theorem tK_eq' : tW.map (evcg (compn 24) (kIdn 24) (tg.map cd)) = tK := by
  rw [tg_codes]
  exact tK_eq

theorem mem_Sg_iff (x : G) : x ∈ Sg ↔ cd x ∈ tK :=
  mem_closure_iff_code cd (compn 24) (kIdn 24) cd_mul cd_one cd_injective tg tW tK tK_eq' Sg_data.2.1
    Sg_data.2.2 x

theorem card_Sg : Nat.card Sg = 1024 := by
  have := card_closure_code cd (compn 24) (kIdn 24) cd_mul cd_one cd_injective tg tW tK tK_eq'
    Sg_data.2.1 Sg_data.2.2 Sg_data.1
  rw [tK_length] at this
  exact this

theorem Sg_isPGroup : IsPGroup 2 ↥Sg := IsPGroup.of_card (n := 10) (by rw [card_Sg]; norm_num)

theorem Sg_sylow : IsSylowTwoOf Sg ⊤ := by
  rw [K1.isSylowTwoOf_top_iff]
  refine ⟨Sg_isPGroup, ?_⟩
  have h := Subgroup.card_mul_index Sg
  rw [card_Sg, CFSG.QuasithinUnique.Ch1.SporLat.M24.m24_card] at h
  have : Sg.index = 239085 := by omega
  rw [this]
  norm_num

section Cosets

variable {H : Type} [Group H] [Finite H]

theorem mem_closure_cosets {S : Subgroup H} (gens W : List H) (h1 : ∃ w ∈ W, w ∈ S)
    (hstep : ∀ w ∈ W, ∀ g ∈ gens, ∃ w' ∈ W, w * g * w'⁻¹ ∈ S) {x : H}
    (hx : x ∈ Subgroup.closure {y | y ∈ gens}) : ∃ w ∈ W, x * w⁻¹ ∈ S := by
  have hP : ∀ x : H, (∃ w ∈ W, x * w⁻¹ ∈ S) → ∀ g ∈ gens, ∃ w ∈ W, x * g * w⁻¹ ∈ S := by
    rintro x ⟨w, hw, hxw⟩ g hg
    obtain ⟨w', hw', hww⟩ := hstep w hw g hg
    refine ⟨w', hw', ?_⟩
    have : x * g * w'⁻¹ = (x * w⁻¹) * (w * g * w'⁻¹) := by group
    rw [this]
    exact S.mul_mem hxw hww
  induction hx using Subgroup.closure_induction_right with
  | one =>
    obtain ⟨w, hw, hws⟩ := h1
    exact ⟨w, hw, by simpa using S.inv_mem hws⟩
  | mul_right x hx y hy ih => exact hP x ih y hy
  | mul_inv_cancel x hx y hy ih =>
    have hy' : y⁻¹ = y ^ (orderOf y - 1) := by
      have h : y ^ (orderOf y - 1) * y = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos y), pow_orderOf_eq_one]
      exact (eq_inv_of_mul_eq_one_left h).symm
    have hpow : ∀ j : ℕ, ∃ w ∈ W, x * y ^ j * w⁻¹ ∈ S := by
      intro j
      induction j with
      | zero => simpa using ih
      | succ j ihj =>
        have := hP _ ihj y hy
        rwa [pow_succ, ← mul_assoc]
    rw [hy']
    exact hpow _

theorem mem_closure_iff_cosets {S : Subgroup H} (gens W : List H)
    (hS : S ≤ Subgroup.closure {y | y ∈ gens}) (hW : ∀ w ∈ W, w ∈ Subgroup.closure {y | y ∈ gens})
    (h1 : ∃ w ∈ W, w ∈ S) (hstep : ∀ w ∈ W, ∀ g ∈ gens, ∃ w' ∈ W, w * g * w'⁻¹ ∈ S) (x : H) :
    x ∈ Subgroup.closure {y | y ∈ gens} ↔ ∃ w ∈ W, x * w⁻¹ ∈ S := by
  refine ⟨mem_closure_cosets gens W h1 hstep, fun ⟨w, hw, hxw⟩ => ?_⟩
  have : x = (x * w⁻¹) * w := by group
  rw [this]
  exact Subgroup.mul_mem _ (hS hxw) (hW w hw)

theorem card_closure_cosets {S : Subgroup H} (gens W : List H)
    (hS : S ≤ Subgroup.closure {y | y ∈ gens}) (hW : ∀ w ∈ W, w ∈ Subgroup.closure {y | y ∈ gens})
    (h1 : ∃ w ∈ W, w ∈ S) (hstep : ∀ w ∈ W, ∀ g ∈ gens, ∃ w' ∈ W, w * g * w'⁻¹ ∈ S)
    (hdist : ∀ i j : Fin W.length, i ≠ j → W[i] * W[j]⁻¹ ∉ S) :
    Nat.card ↥(Subgroup.closure {y | y ∈ gens}) = Nat.card ↥S * W.length := by
  have hiff := mem_closure_iff_cosets gens W hS hW h1 hstep
  let f : ↥S × Fin W.length → ↥(Subgroup.closure {y | y ∈ gens}) := fun p =>
    ⟨p.1 * W[p.2], Subgroup.mul_mem _ (hS p.1.2) (hW _ (List.getElem_mem p.2.2))⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨s, i⟩ ⟨s', j⟩ h
      have h1 : (s : H) * W[i] = s' * W[j] := congrArg Subtype.val h
      have hij : i = j := by
        by_contra hne
        apply hdist i j hne
        have : W[i] * W[j]⁻¹ = (s : H)⁻¹ * s' := by
          calc W[i] * W[j]⁻¹ = (s : H)⁻¹ * ((s : H) * W[i]) * W[j]⁻¹ := by group
            _ = (s : H)⁻¹ * (s' * W[j]) * W[j]⁻¹ := by rw [h1]
            _ = (s : H)⁻¹ * s' := by group
        rw [this]
        exact S.mul_mem (S.inv_mem s.2) s'.2
      subst hij
      have : (s : H) = s' := mul_right_cancel h1
      exact Prod.ext (Subtype.ext this) rfl
    · rintro ⟨z, hz⟩
      obtain ⟨w, hw, hzw⟩ := (hiff z).1 hz
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw
      refine ⟨(⟨z * W[i]⁻¹, hzw⟩, ⟨i, hi⟩), ?_⟩
      apply Subtype.ext
      show z * W[i]⁻¹ * W[i] = z
      group
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod]
  simp

end Cosets

section Pigeon

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.M24


theorem eq_of_card_9216 {Z : Subgroup G} (hZ : m24Ctx.S ≤ Z) (hc : Nat.card ↥Z = 9216) :
    Z = m24Ctx.Y 5 ∨ Z = m24Ctx.Y 10 ∨ Z = m24Ctx.Y 12 := by
  obtain ⟨j, hj, hZeq⟩ := m24_complete Z hZ
  by_cases hj13 : j < 13
  · have hmem : memberOrTop 13 m24Ctx.Y j = m24Ctx.Y j := by simp [memberOrTop, hj13]
    rw [hmem] at hZeq
    rw [hZeq, m24_member_card j hj13] at hc
    interval_cases j <;> simp_all
  · exfalso
    have hj' : j = 13 := by omega
    have hmem : memberOrTop 13 m24Ctx.Y j = ⊤ := by simp [memberOrTop, hj13]
    rw [hmem] at hZeq
    rw [hZeq] at hc
    have h4 : Nat.card (⊤ : Subgroup G) = Nat.card G := Subgroup.card_top
    rw [h4, show Nat.card G = Nat.card ↥NativeSporadic.M24 from rfl, m24_card] at hc
    omega

theorem card_map_conj (g : G) (X : Subgroup G) :
    Nat.card ↥(X.map (MulAut.conj g).toMonoidHom) = Nat.card ↥X :=
  (Nat.card_congr (X.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv).symm

theorem pigeon_four {α : Type*} {a b c z y₁ y₂ y₃ : α} (hA : a = y₁ ∨ a = y₂ ∨ a = y₃)
    (hB : b = y₁ ∨ b = y₂ ∨ b = y₃) (hC : c = y₁ ∨ c = y₂ ∨ c = y₃) (hZ : z = y₁ ∨ z = y₂ ∨ z = y₃)
    (e1 : a ≠ b) (e2 : a ≠ c) (e3 : b ≠ c) (e4 : z ≠ a) (e5 : z ≠ b) (e6 : z ≠ c) : False := by
  rcases hA with h1 | h1 | h1 <;> rcases hB with h2 | h2 | h2 <;> rcases hC with h3 | h3 | h3 <;>
    rcases hZ with h4 | h4 | h4 <;> simp_all

theorem eq_of_three {A B C : Subgroup G} (hSA : Sg ≤ A) (hSB : Sg ≤ B) (hSC : Sg ≤ C)
    (hA : Nat.card ↥A = 9216) (hB : Nat.card ↥B = 9216) (hC : Nat.card ↥C = 9216)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) {Z : Subgroup G} (hSZ : Sg ≤ Z)
    (hZc : Nat.card ↥Z = 9216) : Z = A ∨ Z = B ∨ Z = C := by
  have : Finite G := (CFSG.Sporadic.Mathieu.fam_m24_simplicity).1
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top Sg_sylow m24_S_sylow
  have hmap : ∀ X : Subgroup G, Sg ≤ X → Nat.card ↥X = 9216 →
      X.map (MulAut.conj g).toMonoidHom = m24Ctx.Y 5 ∨ X.map (MulAut.conj g).toMonoidHom = m24Ctx.Y 10 ∨
        X.map (MulAut.conj g).toMonoidHom = m24Ctx.Y 12 := by
    intro X hSX hX
    refine eq_of_card_9216 ?_ ?_
    · rw [← hg]
      exact Subgroup.map_mono hSX
    · rw [card_map_conj]
      exact hX
  have hinj : Function.Injective (Subgroup.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.map_injective (MulAut.conj g).injective
  have hA' := hmap A hSA hA
  have hB' := hmap B hSB hB
  have hC' := hmap C hSC hC
  have hZ' := hmap Z hSZ hZc
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨hZA, hZB, hZC⟩ := hne
  exact pigeon_four hA' hB' hC' hZ'
    (fun h => hAB (hinj h)) (fun h => hAC (hinj h)) (fun h => hBC (hinj h))
    (fun h => hZA (hinj h)) (fun h => hZB (hinj h)) (fun h => hZC (hinj h))

end Pigeon

end CFSG.Quasithin.ModH.M24b
