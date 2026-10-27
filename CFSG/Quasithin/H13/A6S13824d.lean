module

public import CFSG.Quasithin.H13.A6S13824c
public import CFSG.Quasithin.H13.A6S13826e

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace SecHyp

variable {H K X W : Subgroup G} (hs : S.SecHyp H K X W) [IsMulCommutative ↥X]
include hs

theorem sec_pow_two (y : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) : y ^ 2 = 1 := by
  rw [pow_two]; exact hs.sec_sq y

theorem act_eq_of_inv_mul_mem {h k : ↥H} (hq : ((h⁻¹ * k : ↥H) : G) ∈ pCoreOf 2 H) :
    hs.act h = hs.act k := by
  have h1 := (hs.act_eq_one_iff _).2 hq
  rw [map_mul, map_inv] at h1
  exact inv_mul_eq_one.1 h1

theorem not_transv7 {α : ↥K →* alternatingGroup (Fin 7)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) (κ : ↥K)
    {w : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)}
    (ht : IsTransvectionWith (hs.act (Subgroup.inclusion hs.hKH κ)) w)
    (hne : hs.act (Subgroup.inclusion hs.hKH κ) ≠ 1) : False := by
  set actK := hs.act.comp (Subgroup.inclusion hs.hKH) with hactK
  have hE2 := hs.sec_pow_two
  have hactK1 : ∀ k : ↥K, actK k = 1 ↔ α k = 1 := fun k => by
    rw [hαk]
    exact hs.act_eq_one_iff _
  have ht2 : actK κ * actK κ = 1 := B1.tv_sq hE2 ht hne
  have hακ2 : α κ * α κ = 1 := by
    rw [← map_mul, ← hactK1, map_mul]
    exact ht2
  have hακ1 : α κ ≠ 1 := fun h => hne ((hactK1 κ).2 h)
  obtain ⟨γ, hγ⟩ := A7F.isConj_inv (α κ) hακ2 hακ1
  obtain ⟨g, rfl⟩ := hαs γ
  set ka : ↥K := g * κ * g⁻¹ with hka
  have hαka : α ka = ⟨A7F.a7, A7F.a7_mem⟩ := by
    rw [hka, map_mul, map_mul, map_inv]
    exact hγ
  have hta : IsTransvectionWith (actK ka) (actK g w) := by
    have h1 := B1.tv_conj ht (actK g)
    rw [hka, map_mul, map_mul, map_inv]
    exact h1
  have hta1 : actK ka ≠ 1 := by
    rw [Ne, hactK1, hαka]
    intro h
    have := congrArg Subtype.val h
    exact absurd this (by decide)
  obtain ⟨kb, hkb⟩ := hαs ⟨A7F.b7, A7F.b7_mem⟩
  have hsq : ∀ k : ↥K, α k * α k = 1 → actK k * actK k = 1 := fun k hk => by
    rw [← map_mul, hactK1, map_mul]
    exact hk
  have ha2 : actK ka * actK ka = 1 := hsq ka (by rw [hαka]; exact Subtype.ext A7F.a7_sq)
  have hb2 : actK kb * actK kb = 1 := hsq kb (by rw [hkb]; exact Subtype.ext A7F.b7_sq)
  set x := actK ka * actK kb with hx
  have hx5 : x ^ 5 = 1 := by
    rw [hx, ← map_mul, ← map_pow, hactK1, map_pow, map_mul, hαka, hkb]
    exact Subtype.ext A7F.ab7_pow_five
  have hx1 : x ≠ 1 := by
    rw [hx, ← map_mul, Ne, hactK1, map_mul, hαka, hkb]
    intro h
    exact A7F.ab7_ne_one (congrArg Subtype.val h)
  have hinv : actK ka * x * (actK ka)⁻¹ = x⁻¹ := by
    have hai : (actK ka)⁻¹ = actK ka := inv_eq_of_mul_eq_one_right ha2
    have hbi : (actK kb)⁻¹ = actK kb := inv_eq_of_mul_eq_one_right hb2
    rw [hx, hai, mul_inv_rev, hai, hbi, ← mul_assoc, ha2, one_mul]
  obtain ⟨-, -, -, hx3⟩ := B1.inverted_by_transvection hE2 hta hta1 (r := 5) (by decide) hx5
    hx1 hinv
  apply hx1
  calc x = (x ^ 3) ^ 2 * (x ^ 5)⁻¹ := by group
    _ = 1 := by rw [hx3, hx5]; group

theorem card_ge_sixteen7 {α : ↥K →* alternatingGroup (Fin 7)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) :
    16 ≤ Nat.card (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) := by
  set actK := hs.act.comp (Subgroup.inclusion hs.hKH) with hactK
  have hactK1 : ∀ k : ↥K, actK k = 1 ↔ α k = 1 := fun k => by
    rw [hαk]
    exact hs.act_eq_one_iff _
  have hm : A7F.a7 * A7F.b7 ∈ alternatingGroup (Fin 7) :=
    Subgroup.mul_mem _ A7F.a7_mem A7F.b7_mem
  obtain ⟨k, hk⟩ := hαs ⟨A7F.a7 * A7F.b7, hm⟩
  refine B42A57.card_ge_sixteen_of_order_five hs.sec_sq (actK k) ?_ ?_
  · rw [← map_pow, hactK1, map_pow, hk]
    exact Subtype.ext A7F.ab7_pow_five
  · rw [Ne, hactK1, hk]
    intro h
    exact A7F.ab7_ne_one (congrArg Subtype.val h)

omit [Finite G] hs [IsMulCommutative ↥X] in
theorem card_map_rho {ρ : ↥H →* Perm (Fin 7)} (hρ1 : ∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H)
    {F : Subgroup G} (hFH : F ≤ H) :
    Nat.card ((F.subgroupOf H).map ρ) = (F ⊓ pCoreOf 2 H).relIndex F := by
  set ρF : ↥F →* Perm (Fin 7) := ρ.comp (Subgroup.inclusion hFH) with hρF
  have hrange : ρF.range = (F.subgroupOf H).map ρ := by
    ext σ
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨Subgroup.inclusion hFH f, Subgroup.mem_subgroupOf.2 f.2, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, Subgroup.mem_subgroupOf.1 hh⟩, rfl⟩
  have hker : ρF.ker = (F ⊓ pCoreOf 2 H).subgroupOf F := by
    ext f
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hρF, MonoidHom.comp_apply, hρ1]
    exact ⟨fun h => ⟨f.2, h⟩, fun h => h.2⟩
  rw [← hrange, ← Subgroup.index_ker, hker]
  rfl

theorem card_le_index_pow7
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    {α : ↥K →* alternatingGroup (Fin 7)} (hαs : Function.Surjective α)
    {ρ : ↥H →* Perm (Fin 7)} (hρk : ∀ k : ↥K, ρ (Subgroup.inclusion hs.hKH k) = α k)
    (hρ1 : ∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H) {F : Subgroup G} (hFH : F ≤ H)
    (hF : ¬ F ≤ pCoreOf 2 H) (hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' * f⁻¹ * f'⁻¹ ∈ pCoreOf 2 H)
    (hFs : ∀ f ∈ F, f * f ∈ pCoreOf 2 H) :
    ∃ r : ℕ, 2 ≤ r ∧ ((F ⊓ pCoreOf 2 H).relIndex F) ^ r ≤ 2 ^ 6 ∧
      Nat.card (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) ≤
        (fixV (autSec (autOn F X) ⊤ (W.subgroupOf X))).index ^ r := by
  classical
  set B : Subgroup (Perm (Fin 7)) := (F.subgroupOf H).map ρ with hB
  have hρF : ∀ f (hf : f ∈ F), ρ ⟨f, hFH hf⟩ ∈ B := fun f hf =>
    ⟨⟨f, hFH hf⟩, Subgroup.mem_subgroupOf.2 hf, rfl⟩
  have hB1 : B ≠ ⊥ := by
    intro h
    apply hF
    intro f hf
    have h1 := hρF f hf
    rw [h, Subgroup.mem_bot, hρ1] at h1
    exact h1
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨f, hf, rfl⟩ _ ⟨f', hf', rfl⟩
    have h1 := hFc f (Subgroup.mem_subgroupOf.1 hf) f' (Subgroup.mem_subgroupOf.1 hf')
    have h2 : ρ (f * f' * f⁻¹ * f'⁻¹) = 1 := (hρ1 _).2 (by simpa using h1)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc]
    exact h2
  have hB2 : ∀ a ∈ B, a * a = 1 := by
    rintro _ ⟨f, hf, rfl⟩
    rw [← map_mul, hρ1]
    simpa using hFs f (Subgroup.mem_subgroupOf.1 hf)
  obtain ⟨r, fr, hfr, hbound, hcl⟩ := B42A57.gen7 hB1 hBc hB2
  have hcardB : Nat.card B = (F ⊓ pCoreOf 2 H).relIndex F := card_map_rho hρ1 hFH
  have hr2 : 2 ≤ r := by
    by_contra hr
    push Not at hr
    have hab : ∀ x ∈ Subgroup.closure {x | ∃ i, ∃ b ∈ B, x = fr i * b * (fr i)⁻¹},
        ∀ y ∈ Subgroup.closure {x | ∃ i, ∃ b ∈ B, x = fr i * b * (fr i)⁻¹}, x * y = y * x := by
      have hcomm : ({x | ∃ i, ∃ b ∈ B, x = fr i * b * (fr i)⁻¹} : Set (Perm (Fin 7))).Pairwise
          Commute := by
        rintro _ ⟨i, b, hb, rfl⟩ _ ⟨j, b', hb', rfl⟩ -
        have hij : i = j := by
          have hi := i.2
          have hj := j.2
          exact Fin.ext (by omega)
        subst hij
        show fr i * b * (fr i)⁻¹ * (fr i * b' * (fr i)⁻¹) =
          fr i * b' * (fr i)⁻¹ * (fr i * b * (fr i)⁻¹)
        have := hBc b hb b' hb'
        calc fr i * b * (fr i)⁻¹ * (fr i * b' * (fr i)⁻¹) = fr i * (b * b') * (fr i)⁻¹ := by
              group
          _ = fr i * (b' * b) * (fr i)⁻¹ := by rw [this]
          _ = _ := by group
      have := Subgroup.isMulCommutative_closure hcomm
      intro x hx y hy
      have := this.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this
    exact A7F.ab7_ne_ba7 (hab _ (hcl A7F.a7_mem) _ (hcl A7F.b7_mem))
  refine ⟨r, hr2, hcardB ▸ hbound, ?_⟩
  have hki : ∀ i, ∃ k : ↥K, α k = ⟨fr i, hfr i⟩ := fun i => hαs _
  choose k hk using hki
  set A := autSec (autOn F X) ⊤ (W.subgroupOf X) with hA
  let Ci : Fin r → Subgroup (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) := fun i =>
    fixV (A.map (MulAut.conj (hs.act (Subgroup.inclusion hs.hKH (k i)))).toMonoidHom)
  have hC : ⨅ i, Ci i = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hvC : ∀ i, v ∈ Ci i := fun i => (Subgroup.mem_iInf.1 hv) i
    rw [← hs.fixV_eq_bot hirr]
    let St : Subgroup ↥H := (MulAction.stabilizer (MulAut _) v).comap hs.act
    have hStQ : ∀ h : ↥H, (h : G) ∈ pCoreOf 2 H → h ∈ St := fun h hh => by
      show hs.act h • v = v
      rw [(hs.act_eq_one_iff h).2 hh]
      rfl
    have hconj : ∀ i, ∀ f (hf : f ∈ F), (Subgroup.inclusion hs.hKH (k i)) * ⟨f, hFH hf⟩ *
        (Subgroup.inclusion hs.hKH (k i))⁻¹ ∈ St := by
      intro i f hf
      have hmem : hs.act (Subgroup.inclusion hs.hKH (k i)) * hs.act ⟨f, hFH hf⟩ *
          (hs.act (Subgroup.inclusion hs.hKH (k i)))⁻¹ ∈
          A.map (MulAut.conj (hs.act (Subgroup.inclusion hs.hKH (k i)))).toMonoidHom :=
        ⟨_, (hs.mem_autSec_iff hFH).2 ⟨⟨f, hFH hf⟩, hf, rfl⟩, by simp⟩
      have := hvC i _ hmem
      show hs.act _ • v = v
      rw [map_mul, map_mul, map_inv]
      exact this
    have hcl' : Subgroup.closure {x | ∃ i, ∃ b ∈ B, x = fr i * b * (fr i)⁻¹} ≤ St.map ρ := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, _, ⟨f, hf, rfl⟩, rfl⟩
      refine ⟨_, hconj i f (Subgroup.mem_subgroupOf.1 hf), ?_⟩
      rw [map_mul, map_mul, map_inv, hρk, hk]
    intro ψ hψ
    obtain ⟨κ, hκK, rfl⟩ := (hs.mem_autSec_iff hs.hKH).1 hψ
    obtain ⟨s, hsSt, hsρ⟩ := hcl' (hcl (α ⟨κ, hκK⟩).2)
    have hq : ((s⁻¹ * κ : ↥H) : G) ∈ pCoreOf 2 H := by
      rw [← hρ1, map_mul, map_inv, hsρ]
      have := hρk ⟨κ, hκK⟩
      rw [show Subgroup.inclusion hs.hKH ⟨(κ : G), hκK⟩ = κ from Subtype.ext rfl] at this
      rw [this, inv_mul_cancel]
    rw [← hs.act_eq_of_inv_mul_mem hq]
    exact hsSt
  have h1 := Subgroup.index_iInf_le Ci
  rw [hC, Subgroup.index_bot] at h1
  have h2 : ∀ i, (Ci i).index = (fixV A).index := fun i => B42A57.index_fixV_conj A _
  simp only [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  exact h1

end SecHyp

end Setting4

end CFSG.Quasithin.H13.A6
