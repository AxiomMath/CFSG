module

public import CFSG.Quasithin.AppendixH.H15.H157Nt

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH.H157

open CFSG.Quasithin CFSG.Quasithin.H153 CFSG.Quasithin.H.Coc24 CFSG.ASVolI.ChH CFSG.Monster.Code


theorem mem_normalizer_of_mem_normalizer_subgroupOf {G : Type*} [Group G] {H K : Subgroup G}
    (hHK : H ≤ K) {a : ↥K}
    (ha : a ∈ Subgroup.normalizer ((H.subgroupOf K : Subgroup ↥K) : Set ↥K)) :
    (a : G) ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 := (Subgroup.mem_normalizer_iff.1 ha (⟨x, hHK hx⟩ : ↥K)).1
      (Subgroup.mem_subgroupOf.2 hx)
    exact Subgroup.mem_subgroupOf.1 h1
  · intro hx
    have hxK : a * x * a⁻¹ ∈ K := hHK hx
    have hxK' : x ∈ K := by
      have := K.mul_mem (K.mul_mem (K.inv_mem a.2) hxK) a.2
      simpa [mul_assoc] using this
    have h1 := (Subgroup.mem_normalizer_iff.1 ha (⟨x, hxK'⟩ : ↥K)).2
      (Subgroup.mem_subgroupOf.2 (by simpa using hx))
    exact Subgroup.mem_subgroupOf.1 h1

theorem subgroupOf_zpowers_eq_zpowers {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ H) :
    (Subgroup.zpowers g).subgroupOf H = Subgroup.zpowers (⟨g, hg⟩ : ↥H) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by have := congrArg Subtype.val hk; rwa [Subgroup.coe_zpow] at this⟩

theorem MY0_le_Nt_sup_KSp : MY M24g S0 ≤ (Nt ⊓ MY M24g S0) ⊔ KSp := by
  intro σ hσ
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set tG : ↥(MY M24g S0) := ⟨tP, tP_mem_MY0⟩ with htG
  set tN : ↥(piM.ker) := ⟨tG, piM_tP⟩ with htN
  set P0 : Subgroup ↥(piM.ker) := Subgroup.zpowers tN with hP0
  have horder : orderOf tN = 3 := by
    have h1 : orderOf tN = orderOf tG := by
      rw [← Subgroup.orderOf_coe tN, htN]
    have h2 : orderOf tG = 3 := by
      rw [← Subgroup.orderOf_coe tG]
      show orderOf tP = 3
      exact orderOf_tP
    exact h1.trans h2
  have hcard : Nat.card P0 = 3 ^ (Nat.card ↥(piM.ker)).factorization 3 := by
    rw [hP0, Nat.card_zpowers, horder, card_ker_piM]
    have hf : (192 : ℕ).factorization 3 = 1 := by decide +kernel
    rw [hf]
    norm_num
  set P : Sylow 3 ↥(piM.ker) := Sylow.ofCard P0 hcard with hPs
  have hcoP : (↑P : Subgroup ↥(piM.ker)) = Subgroup.zpowers tN := Sylow.coe_ofCard P0 hcard
  have hmap : Subgroup.map (piM.ker).subtype ↑P = Subgroup.zpowers tG := by
    rw [hcoP, MonoidHom.map_zpowers]
    rfl
  have hfr := Sylow.normalizer_sup_eq_top P
  rw [hmap] at hfr
  have hg : (⟨σ, hσ⟩ : ↥(MY M24g S0)) ∈
      Subgroup.normalizer ↑(Subgroup.zpowers tG) ⊔ piM.ker := by
    rw [hfr]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, n, hn, heq⟩ := (Subgroup.mem_sup_of_normal_right).1 hg
  have hsub : (Subgroup.zpowers tP).subgroupOf (MY M24g S0) = Subgroup.zpowers tG := by
    rw [htG]
    exact subgroupOf_zpowers_eq_zpowers tP_mem_MY0
  have haN : (a : S24) ∈ Subgroup.normalizer (Subgroup.zpowers tP : Set S24) := by
    refine mem_normalizer_of_mem_normalizer_subgroupOf (H := Subgroup.zpowers tP)
      (K := MY M24g S0) (Subgroup.zpowers_le.2 tP_mem_MY0) ?_
    rw [hsub]
    exact ha
  have haNt : (a : S24) ∈ Nt ⊓ MY M24g S0 :=
    ⟨⟨MY0_le_autPerm a.property, haN⟩, a.property⟩
  have hzp : Subgroup.zpowers tP ≤ Nt ⊓ MY M24g S0 :=
    le_inf zpowers_tP_le_Nt (Subgroup.zpowers_le.2 tP_mem_MY0)
  have hnN0 : (n : S24) ∈ N0 :=
    mem_N0.2 ⟨n.property, MonoidHom.mem_ker.1 hn⟩
  have hnSup : (n : S24) ∈ (Nt ⊓ MY M24g S0) ⊔ KSp := by
    have h1 : (n : S24) ∈ KSp ⊔ Subgroup.zpowers tP := by
      rw [← N0_eq_sup]
      exact hnN0
    have h2 : KSp ⊔ Subgroup.zpowers tP ≤ KSp ⊔ (Nt ⊓ MY M24g S0) :=
      sup_le_sup_left hzp KSp
    have h3 := h2 h1
    rwa [sup_comm] at h3
  have hprod : (a : S24) * (n : S24) ∈ (Nt ⊓ MY M24g S0) ⊔ KSp :=
    ((Nt ⊓ MY M24g S0) ⊔ KSp).mul_mem (Subgroup.mem_sup_left haNt) hnSup
  have hσeq : (a : S24) * (n : S24) = σ := by
    have h := congrArg (fun x : ↥(MY M24g S0) => (x : S24)) heq
    simpa only [Subgroup.coe_mul] using h
  rw [← hσeq]
  exact hprod

theorem card_Nt_inf_MY0 : Nat.card ↥(Nt ⊓ MY M24g S0) = 2160 := by
  have htop : (Nt ⊓ MY M24g S0).subgroupOf (MY M24g S0) ⊔
      KSp.subgroupOf (MY M24g S0) = ⊤ := by
    apply Subgroup.map_injective (MY M24g S0).subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le inf_le_right,
      Subgroup.map_subgroupOf_eq_of_le KSp_le_MY0, Subgroup.map_top, Subgroup.range_subtype]
    exact le_antisymm (sup_le inf_le_right KSp_le_MY0) MY0_le_Nt_sup_KSp
  have hdisj : Disjoint ((Nt ⊓ MY M24g S0).subgroupOf (MY M24g S0))
      (KSp.subgroupOf (MY M24g S0)) := by
    rw [disjoint_iff_inf_le]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hx1 : (x : S24) ∈ Nt ⊓ MY M24g S0 := Subgroup.mem_subgroupOf.1 hx.1
    have hx2 : (x : S24) ∈ KSp := Subgroup.mem_subgroupOf.1 hx.2
    have hxk : (x : S24) ∈ Nt ⊓ KSp := ⟨hx1.1, hx2⟩
    rw [Nt_inf_KSp, Subgroup.mem_bot] at hxk
    exact Subgroup.mem_bot.2 (Subtype.ext (by simpa using hxk))
  haveI hnorm : (KSp.subgroupOf (MY M24g S0)).Normal := ⟨fun k hk g => by
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using MY0_conj_KSp g.property hk⟩
  have hmul : (↑((Nt ⊓ MY M24g S0).subgroupOf (MY M24g S0)) : Set ↥(MY M24g S0)) *
      (↑(KSp.subgroupOf (MY M24g S0)) : Set ↥(MY M24g S0)) = Set.univ := by
    rw [← Subgroup.mul_normal ((Nt ⊓ MY M24g S0).subgroupOf (MY M24g S0))
      (KSp.subgroupOf (MY M24g S0)), htop]
    rfl
  have hcomp : ((Nt ⊓ MY M24g S0).subgroupOf (MY M24g S0)).IsComplement'
      (KSp.subgroupOf (MY M24g S0)) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  have hcard := hcomp.card_mul
  rw [card_MY0] at hcard
  have hKcard : Nat.card ↥(KSp.subgroupOf (MY M24g S0)) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe KSp_le_MY0).toEquiv, card_KSp]
  have hHcard : Nat.card ↥((Nt ⊓ MY M24g S0).subgroupOf (MY M24g S0)) =
      Nat.card ↥(Nt ⊓ MY M24g S0) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
  rw [hKcard, hHcard] at hcard
  omega

theorem Nt_le_MY0 : Nt ≤ MY M24g S0 := by
  have h : Nt ⊓ MY M24g S0 = Nt :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [card_Nt_inf_MY0]; exact card_Nt_le)
  rw [← h]
  exact inf_le_right

theorem card_Nt : Nat.card ↥Nt = 2160 := by
  have h : Nt ⊓ MY M24g S0 = Nt :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [card_Nt_inf_MY0]; exact card_Nt_le)
  rw [← h, card_Nt_inf_MY0]

theorem Nt_sup_KSp : Nt ⊔ KSp = MY M24g S0 := by
  refine le_antisymm (sup_le Nt_le_MY0 KSp_le_MY0) ?_
  have h : Nt ⊓ MY M24g S0 = Nt := inf_eq_left.2 Nt_le_MY0
  rw [← h]
  exact MY0_le_Nt_sup_KSp

theorem exists_pi_Nt :
    ∃ π : ↥Nt →* Equiv.Perm (Fin 6), Function.Surjective π ∧
      π.ker = (Subgroup.zpowers tP).subgroupOf Nt ∧
      ∀ (n : ↥Nt) (j : Fin 6), (n : S24) (fixPt j) = fixPt (π n j) := by
  let π : ↥Nt →* Equiv.Perm (Fin 6) := piM.comp (Subgroup.inclusion Nt_le_MY0)
  have hcol : ∀ (n : ↥Nt) (i : Fin 24), colOf ((n : S24) i) = π n (colOf i) := by
    intro n i
    have h := colHom_spec (Subgroup.inclusion MY0_le_BP
      (Subgroup.inclusion Nt_le_MY0 n)) i
    simpa [π, piM, MonoidHom.comp_apply] using h
  let tNt : ↥Nt := ⟨tP, zpowers_tP_le_Nt (Subgroup.mem_zpowers tP)⟩
  have hker : π.ker = (Subgroup.zpowers tP).subgroupOf Nt := by
    apply le_antisymm
    · intro n hn
      have hnker : π n = 1 := MonoidHom.mem_ker.1 hn
      rw [Subgroup.mem_subgroupOf]
      have hN0 : (n : S24) ∈ N0 := by
        refine mem_N0.2 ⟨Nt_le_MY0 n.property, ?_⟩
        show piM (Subgroup.inclusion Nt_le_MY0 n) = 1
        exact hnker
      set m : ↥N0 := ⟨(n : S24), hN0⟩ with hm
      haveI hKn : (KSp.subgroupOf N0).Normal := ⟨fun k hk g => by
        rw [Subgroup.mem_subgroupOf] at hk ⊢
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
          MY0_conj_KSp (N0_le_MY0 g.property) hk⟩
      have hsup : (KSp.subgroupOf N0) ⊔ ((Subgroup.zpowers tP).subgroupOf N0) = ⊤ := by
        apply Subgroup.map_injective N0.subtype_injective
        rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le KSp_le_N0,
          Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.2 tP_mem_N0),
          Subgroup.map_top, Subgroup.range_subtype]
        exact N0_eq_sup.symm
      have hm' : m ∈ (KSp.subgroupOf N0) ⊔ ((Subgroup.zpowers tP).subgroupOf N0) := by
        rw [hsup]
        exact Subgroup.mem_top m
      obtain ⟨k, hk, u, hu, hku⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := KSp.subgroupOf N0)).1 hm'
      have hkK : (k : S24) ∈ KSp := Subgroup.mem_subgroupOf.1 hk
      have huZ : (u : S24) ∈ Subgroup.zpowers tP := Subgroup.mem_subgroupOf.1 hu
      have hkm : (k : S24) = (n : S24) * (u : S24)⁻¹ := by
        have h : (k : S24) * (u : S24) = (n : S24) := by
          have := congrArg (fun x : ↥N0 => (x : S24)) hku
          simpa only [Subgroup.coe_mul, hm] using this
        rw [← h]
        group
      have hkNt : (k : S24) ∈ Nt := by
        rw [hkm]
        exact Nt.mul_mem n.property (Nt.inv_mem (zpowers_tP_le_Nt huZ))
      have hk1 : (k : S24) = 1 := by
        have hk' : (k : S24) ∈ Nt ⊓ KSp := ⟨hkNt, hkK⟩
        rwa [Nt_inf_KSp, Subgroup.mem_bot] at hk'
      have hnu : (n : S24) = (u : S24) := by
        have h : (n : S24) * (u : S24)⁻¹ = 1 := by rw [← hkm, hk1]
        calc (n : S24) = (n : S24) * (u : S24)⁻¹ * (u : S24) := by group
          _ = 1 * (u : S24) := by rw [h]
          _ = (u : S24) := by group
      rwa [hnu]
    · rw [subgroupOf_zpowers_eq_zpowers (zpowers_tP_le_Nt (Subgroup.mem_zpowers tP))]
      apply Subgroup.zpowers_le.2
      rw [MonoidHom.mem_ker]
      change piM (Subgroup.inclusion Nt_le_MY0 tNt) = 1
      rw [show Subgroup.inclusion Nt_le_MY0 tNt =
          (⟨tP, tP_mem_MY0⟩ : ↥(MY M24g S0)) from Subtype.ext rfl]
      exact piM_tP
  have hfix : ∀ (n : ↥Nt) (j : Fin 6), (n : S24) (fixPt j) = fixPt (π n j) := by
    intro n j
    have hntfix : (n : S24) (fixPt j) ∈ tFix :=
      (mem_tFix_iff_of_mem_Nt n.property (fixPt j)).2 (fixPt_mem_tFix j)
    rw [eq_fixPt_colOf hntfix]
    congr 1
    rw [hcol n (fixPt j), colOf_fixPt]
  have hker_card : Nat.card ↥π.ker = 3 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe zpowers_tP_le_Nt).toEquiv,
      Nat.card_zpowers, orderOf_tP]
  have hsurj : Function.Surjective π := by
    have hrange_card : Nat.card ↥π.range = 720 := by
      have h := Subgroup.card_ker_mul_card_range π
      rw [hker_card, card_Nt] at h
      omega
    have htop : π.range = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hrange_card, card_perm_six]
    exact MonoidHom.range_eq_top.1 htop
  exact ⟨π, hsurj, hker, hfix⟩

end CFSG.ASVolI.AppH.H157
