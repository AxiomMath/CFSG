module

public import CFSG.Quasithin.H13.A6S13824k
public import CFSG.Quasithin.H13.A6S13824d
public import CFSG.Quasithin.H13.A6S13824j

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open scoped IsMulCommutative commutatorElement

namespace A7F

theorem vecS_45 : A6L76.vecS 7 {4, 5} = pvm 4 5 := by decide +kernel

theorem vecS_46 : A6L76.vecS 7 {4, 6} = pvm 4 6 := by decide +kernel

theorem mk7_injective : Function.Injective (QuotientGroup.mk : ↥(FFModel.altDn 7).sec →
    ↥(FFModel.altDn 7).sec ⧸ (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec) := by
  intro a b h
  have h1 : a⁻¹ * b ∈ (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec :=
    QuotientGroup.eq.1 h
  rw [QuasithinUnique.B42A57.altDn7_ker, Subgroup.bot_subgroupOf] at h1
  exact inv_mul_eq_one.1 (Subgroup.mem_bot.1 h1)

end A7F

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace DK

variable {H K : Subgroup G} (hd : S.DK H K)
include hd

theorem comm_V3_mem {r : G} (hr : r ∈ pCoreOf 2 (S.L1 ⊔ T)) {v : G} (hv : v ∈ S.V3) :
    r * v * r⁻¹ * v⁻¹ ∈ fsuV1 T V := by
  have hF := (hd.hS.hF H hd.hH).toHypF91
  have : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    ⟨hF.isElemAbelian_tilde⟩
  have hV₁ := hF.H_normalizes_V₁
  have hIH := le_normalizer_conjClosure S.V3 H
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have hrH : r ∈ H := hF.L₁T_le_H (pCoreOf_le 2 _ hr)
  have hvU : v ∈ conjClosure S.V3 H := le_conjClosure S.V3 H hv
  have hw := (modMk_mem_subM_iff hIHN hF.V₁_le_Vp hvU).2 hv
  have h1 := S.R1_fix_tilde_V3 hd.hS hd.hH hV₁ hIH (r := ⟨r, hrH⟩) hr hw
  rw [actH_modMk hV₁ hIHN hIH] at h1
  have h2 : (r * v * r⁻¹)⁻¹ * v ∈ fsuV1 T V := secMk_eq_secMk_iff.1 (congrArg Subtype.val h1)
  have h3 : v * ((r * v * r⁻¹)⁻¹ * v)⁻¹ * v⁻¹ ∈ fsuV1 T V :=
    (Subgroup.mem_normalizer_iff.mp (hIHN hvU) _).mp ((fsuV1 T V).inv_mem h2)
  have e : v * ((r * v * r⁻¹)⁻¹ * v)⁻¹ * v⁻¹ = r * v * r⁻¹ * v⁻¹ := by group
  rwa [e] at h3

theorem false_of_D7 [IsMulCommutative ↥(conjClosure S.V3 H)]
    (hhat : IsHatA6 L)
    {π : (FFModel.altDn 7).Gam →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    {β : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) →*
      ↥(FFModel.altDn 7).sec ⧸ (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec}
    (hR : CFSG.Quasithin.H.Mathieu.RealizesBy (FFModel.altDn 7)
      (autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) π β)
    (hV3 : A6L76.MapsOnto β ((S.V3.subgroupOf (conjClosure S.V3 H)).map
        (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      ([1, A6L76.vecS 7 {4, 5}, A6L76.vecS 7 {4, 6}, A6L76.vecS 7 {5, 6}] :
        List (FFModel.altDn 7).Amb))
    (hcase : (∃ x ∈ pCoreOf 2 (S.L1 ⊔ T),
        InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V)) ∨
      ∃ Y : Subgroup G, Y ≤ pCoreOf 2 (S.L1 ⊔ T) ∧ ⁅⁅conjClosure S.V3 H, Y⁆, Y⁆ = ⊥ ∧
        4 ≤ (Y ⊓ pCoreOf 2 H).relIndex Y) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF1 := hd.hF.toHypF91
  have hsV := hd.secU le_rfl hd.V1_lt_UH.le le_rfl (le_normalizer_conjClosure _ _)
    hF1.H_normalizes_V₁ (hd.knt_top hd.V1_lt_UH)
  have hcomm : commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊤ := hd.commV_autSec_eq_top
  have hU : ∀ e, e ∈ commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := fun e => hcomm ▸ Subgroup.mem_top e
  obtain ⟨ρ, hρ1, hρβ⟩ := hd.exists_perm7 hsV hR
  obtain ⟨-, -, -, -, -, -, -, hβs, -, -⟩ := hR
  have hβc : ∀ (x : ↥H) (u : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))) (m : ↥(G6.coreMod 7)),
      β u = QuotientGroup.mk m →
      β ⟨hsV.act x u * (↑u)⁻¹, hU _⟩ = QuotientGroup.mk
        (⟨G6.permAct 7 (ρ x) m, G6.permAct_mem_coreMod (ρ x) m.2⟩ * m⁻¹) := by
    intro x u m hm
    have e : (⟨hsV.act x u * (↑u)⁻¹, hU _⟩ : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))) = ⟨hsV.act x u, hU _⟩ * u⁻¹ := rfl
    rw [e, map_mul, map_inv, hρβ x u m (hU _) hm, hm]
    rfl
  have hP_H : ∀ p ∈ pCoreOf 2 (S.L1 ⊔ T), p ∈ H := fun p hp =>
    hF1.L₁T_le_H (pCoreOf_le 2 _ hp)
  have hfix456 : ∀ x : ↥H, (∀ v ∈ S.V3, (x : G) * v * (x : G)⁻¹ * v⁻¹ ∈ fsuV1 T V) →
      ρ x 4 = 4 ∧ ρ x 5 = 5 ∧ ρ x 6 = 6 := by
    intro x hx
    have key : ∀ w ∈ ([1, A6L76.vecS 7 {4, 5}, A6L76.vecS 7 {4, 6}, A6L76.vecS 7 {5, 6}] :
        List (FFModel.altDn 7).Amb), G6.permAct 7 (ρ x) w = w := by
      intro w hw
      obtain ⟨y, hyW, m, hym, hmw⟩ := hV3.2 w hw
      obtain ⟨⟨v, hvU⟩, hv3, hyv⟩ := hyW
      have hact : hsV.act x y = y := by
        rw [← hyv, SecHyp.act_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul,
          A6Mod.secMk_eq_one_iff]
        simpa [Setup.rho_apply_coe] using hx v (Subgroup.mem_subgroupOf.1 hv3)
      have h1 := hρβ x y m (hU _) hym
      have e : (⟨hsV.act x y, hU _⟩ : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))) = y := Subtype.ext hact
      rw [e, hym] at h1
      have h3 := congrArg Subtype.val (A7F.mk7_injective h1)
      rw [← hmw]
      exact h3.symm
    have h45 := key (A6L76.vecS 7 {4, 5}) (List.mem_cons_of_mem _ List.mem_cons_self)
    have h46 := key (A6L76.vecS 7 {4, 6})
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    rw [A7F.vecS_45] at h45
    rw [A7F.vecS_46] at h46
    exact A7F.fix456_of_fix h45 h46
  obtain ⟨c, hcl0, hc3, hcO, -⟩ := exists_l0_c hhat.2.1
  have hcL1 : c ∈ S.L1 := S.l0_le_L1 hcl0
  have hcH : c ∈ H := hF1.L₁T_le_H (Subgroup.mem_sup_left hcL1)
  have hcV : c ∈ Subgroup.centralizer (V : Set G) := S.o2Z_le_centralizer (oTwoRes_le _ hcl0)
  have hcfix := hfix456 ⟨c, hcH⟩ fun v hv => by
    have h1 := Subgroup.mem_centralizer_iff.1 hcV v (S.V3_le_V hv)
    have e : c * v * c⁻¹ * v⁻¹ = 1 := by rw [← h1]; group
    rw [e]
    exact (fsuV1 T V).one_mem
  have hc1 : ρ ⟨c, hcH⟩ ≠ 1 := by
    intro h1
    have hcQ := (hρ1 _).1 h1
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 H) ⟨c, hcQ⟩
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact hcO (by rw [A7F.eq_one_of_pow_three hc3 hk']; exact (pCoreOf 2 L).one_mem)
  have hc3' : ρ ⟨c, hcH⟩ ^ 3 = 1 := by
    rw [← map_pow]
    convert map_one ρ
    exact Subtype.ext (by simp [hc3])
  have hcP : ∀ p ∈ pCoreOf 2 (S.L1 ⊔ T), c * p * c⁻¹ ∈ pCoreOf 2 (S.L1 ⊔ T) ∧
      c⁻¹ * p * c ∈ pCoreOf 2 (S.L1 ⊔ T) := by
    intro p hp
    have hcN := le_normalizer_pCoreOf 2 (S.L1 ⊔ T) (Subgroup.mem_sup_left hcL1)
    have hcN' := le_normalizer_pCoreOf 2 (S.L1 ⊔ T)
      ((S.L1 ⊔ T).inv_mem (Subgroup.mem_sup_left hcL1))
    refine ⟨(Subgroup.mem_normalizer_iff.mp hcN p).mp hp, ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp hcN' p).mp hp
    simpa using this
  have h2P : ∀ p : ↥H, (p : G) ∈ pCoreOf 2 (S.L1 ⊔ T) → ∃ k : ℕ, ρ p ^ 2 ^ k = 1 := by
    intro p hp
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (S.L1 ⊔ T)) ⟨p, hp⟩
    refine ⟨k, ?_⟩
    rw [← map_pow]
    convert map_one ρ
    exact Subtype.ext (by simpa using congrArg Subtype.val hk)
  have hK4 : ∀ p : ↥H, (p : G) ∈ pCoreOf 2 (S.L1 ⊔ T) → ρ p = 1 ∨ A7F.InK4 (ρ p) := by
    intro p hp
    obtain ⟨h4, h5, h6⟩ := hfix456 p fun v hv => hd.comm_V3_mem hp hv
    obtain ⟨k, hk⟩ := h2P p hp
    rcases A7F.two_elem_fix456 h4 h5 h6 hcfix.1 hcfix.2.1 hcfix.2.2 hc3' hc1
        (A7F.pow_four_of_fix h4 h5 h6 hk) with h | h | h | h | ⟨w, hw, hw3, hw1⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exfalso
      have hpc := hcP p hp
      have hq : ∃ q : ↥H, (q : G) ∈ pCoreOf 2 (S.L1 ⊔ T) ∧ ρ q = w := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨p * ((⟨c, hcH⟩ : ↥H) * p * (⟨c, hcH⟩ : ↥H)⁻¹),
            (pCoreOf 2 (S.L1 ⊔ T)).mul_mem hp hpc.1, by simp [map_mul, map_inv]⟩
        · exact ⟨p * ((⟨c, hcH⟩ : ↥H)⁻¹ * p * (⟨c, hcH⟩ : ↥H)),
            (pCoreOf 2 (S.L1 ⊔ T)).mul_mem hp hpc.2, by simp [map_mul, map_inv]⟩
        · exact ⟨p * p * ((⟨c, hcH⟩ : ↥H) * p * (⟨c, hcH⟩ : ↥H)⁻¹),
            (pCoreOf 2 (S.L1 ⊔ T)).mul_mem ((pCoreOf 2 (S.L1 ⊔ T)).mul_mem hp hp) hpc.1,
            by simp [map_mul, map_inv]⟩
        · exact ⟨((⟨c, hcH⟩ : ↥H) * p * (⟨c, hcH⟩ : ↥H)⁻¹) *
              ((⟨c, hcH⟩ : ↥H)⁻¹ * p * (⟨c, hcH⟩ : ↥H)),
            (pCoreOf 2 (S.L1 ⊔ T)).mul_mem hpc.1 hpc.2, by simp [map_mul, map_inv]⟩
      obtain ⟨q, hqP, rfl⟩ := hq
      obtain ⟨k', hk'⟩ := h2P q hqP
      exact hw1 (A7F.eq_one_of_pow_three hw3 hk')
  have hcomm_el : ∀ (x : ↥H) (u : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))), ∃ ũ : ↥(conjClosure S.V3 H),
      hsV.act x u * (↑u)⁻¹ = InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
        (Setup.rho (conjClosure S.V3 H) H hsV.hHX x ũ * ũ⁻¹) := by
    intro x u
    obtain ⟨ũ, hũ⟩ := InternalSec.secMk_surjective
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) (u : _)
    refine ⟨ũ, ?_⟩
    rw [← hũ, SecHyp.act_secMk, map_mul, map_inv]
  rcases hcase with ⟨x, hxP, hxt⟩ | ⟨Y, hYP, hYq, hY4⟩
  ·
    obtain ⟨hnot, z, hz⟩ := hxt
    have hxH := hP_H x hxP
    rcases hK4 ⟨x, hxH⟩ hxP with h1 | hσ
    · have hxQ := (hρ1 _).1 h1
      rw [hF1.pCoreOf_eq_centralizerMod] at hxQ
      exact hnot hxQ.2.2
    obtain ⟨j, hj1, hj2, hj12⟩ := A7F.not_transv_K4 hσ
    obtain ⟨u₁, hu₁⟩ := hβs (QuotientGroup.mk ⟨A7F.pvm 0 4, B45Alt7.pv_mem_coreMod 0 4⟩)
    obtain ⟨u₂, hu₂⟩ := hβs (QuotientGroup.mk ⟨A7F.pvm j 4, B45Alt7.pv_mem_coreMod j 4⟩)
    have hd₁ := hβc ⟨x, hxH⟩ u₁ _ hu₁
    have hd₂ := hβc ⟨x, hxH⟩ u₂ _ hu₂
    obtain ⟨ũ₁, he₁⟩ := hcomm_el ⟨x, hxH⟩ u₁
    obtain ⟨ũ₂, he₂⟩ := hcomm_el ⟨x, hxH⟩ u₂
    have hn : ∀ (u : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))) (ũ : ↥(conjClosure S.V3 H))
        (m : ↥(G6.coreMod 7)),
        hsV.act ⟨x, hxH⟩ u * (↑u)⁻¹ = InternalSec.secMk
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
          (Setup.rho (conjClosure S.V3 H) H hsV.hHX ⟨x, hxH⟩ ũ * ũ⁻¹) →
        β ⟨hsV.act ⟨x, hxH⟩ u * (↑u)⁻¹, hU _⟩ = QuotientGroup.mk m → m ≠ 1 →
        x * ũ * x⁻¹ * (ũ : G)⁻¹ ∉ fsuV1 T V := by
      intro u ũ m he hβm hm1 hmem
      have h0 : hsV.act ⟨x, hxH⟩ u * (↑u)⁻¹ = 1 := by
        rw [he, A6Mod.secMk_eq_one_iff]
        simpa [Setup.rho_apply_coe] using hmem
      have h0' : (⟨hsV.act ⟨x, hxH⟩ u * (↑u)⁻¹, hU _⟩ :
          ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))) = 1 := Subtype.ext h0
      rw [h0', map_one] at hβm
      exact hm1 (A7F.mk7_injective (hβm.symm.trans (map_one (QuotientGroup.mk' _)).symm))
    have hn₁ := hn u₁ ũ₁ _ he₁ hd₁ fun h => hj1 (congrArg Subtype.val h)
    have hn₂ := hn u₂ ũ₂ _ he₂ hd₂ fun h => hj2 (congrArg Subtype.val h)
    have hz₁ := (hz _ ũ₁.2).resolve_left hn₁
    have hz₂ := (hz _ ũ₂.2).resolve_left hn₂
    have heq : hsV.act ⟨x, hxH⟩ u₁ * (↑u₁)⁻¹ = hsV.act ⟨x, hxH⟩ u₂ * (↑u₂)⁻¹ := by
      rw [he₁, he₂, ← mul_inv_eq_one, ← map_inv, ← map_mul, A6Mod.secMk_eq_one_iff]
      have e : (((Setup.rho (conjClosure S.V3 H) H hsV.hHX ⟨x, hxH⟩ ũ₁ * ũ₁⁻¹) *
          (Setup.rho (conjClosure S.V3 H) H hsV.hHX ⟨x, hxH⟩ ũ₂ * ũ₂⁻¹)⁻¹ :
            ↥(conjClosure S.V3 H)) : G) =
          (x * ũ₁ * x⁻¹ * (ũ₁ : G)⁻¹ * z⁻¹) * (x * ũ₂ * x⁻¹ * (ũ₂ : G)⁻¹ * z⁻¹)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe]
        group
      rw [e]
      exact (fsuV1 T V).mul_mem hz₁ ((fsuV1 T V).inv_mem hz₂)
    have h0 : (⟨hsV.act ⟨x, hxH⟩ u₁ * (↑u₁)⁻¹, hU _⟩ :
        ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))) =
        ⟨hsV.act ⟨x, hxH⟩ u₂ * (↑u₂)⁻¹, hU _⟩ := Subtype.ext heq
    rw [h0, hd₂] at hd₁
    exact hj12 (congrArg Subtype.val (A7F.mk7_injective hd₁)).symm
  ·
    have hYH : Y ≤ H := fun y hy => hP_H y (hYP hy)
    rw [← SecHyp.card_map_rho hρ1 hYH] at hY4
    have hcardle : ∀ σ₀ : Perm (Fin 7), (∀ b : ↥H, (b : G) ∈ Y → ρ b = 1 ∨ ρ b = σ₀) →
        False := by
      intro σ₀ hσ₀
      have hsub : (((Y.subgroupOf H).map ρ : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) ⊆
          {1, σ₀} := by
        rintro _ ⟨b, hb, rfl⟩
        rcases hσ₀ b (Subgroup.mem_subgroupOf.1 hb) with h | h
        · exact Or.inl h
        · exact Or.inr h
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 : ({1, σ₀} : Set (Perm (Fin 7))).ncard ≤ 2 :=
        (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
      have h3 : Nat.card ↥((Y.subgroupOf H).map ρ) =
          (((Y.subgroupOf H).map ρ : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))).ncard :=
        Nat.card_coe_set_eq _
      omega
    obtain ⟨a, haY, ha1⟩ : ∃ a : ↥H, (a : G) ∈ Y ∧ ρ a ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hcardle 1 fun b hb => Or.inl (hcon b hb)
    obtain ⟨b, hbY, hb1, hab⟩ : ∃ b : ↥H, (b : G) ∈ Y ∧ ρ b ≠ 1 ∧ ρ a ≠ ρ b := by
      by_contra hcon
      push Not at hcon
      exact hcardle (ρ a) fun b hb => by
        by_cases h : ρ b = 1
        · exact Or.inl h
        · exact Or.inr (hcon b hb h).symm
    have hσa := (hK4 a (hYP haY)).resolve_left ha1
    have hσb := (hK4 b (hYP hbY)).resolve_left hb1
    have hq := A7F.not_quad_K4 hσa hσb hab
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨A7F.pvm 0 4, B45Alt7.pv_mem_coreMod 0 4⟩)
    have hd₁ := hβc a u _ hu
    have hd₂ := hβc b ⟨hsV.act a u * (↑u)⁻¹, hU _⟩ _ hd₁
    obtain ⟨ũ, hũ⟩ := InternalSec.secMk_surjective
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) (u : _)
    have hdc : (a : G) * ũ * (a : G)⁻¹ * (ũ : G)⁻¹ ∈ ⁅conjClosure S.V3 H, Y⁆ := by
      have h1 := Subgroup.commutator_mem_commutator ũ.2 haY
      have e : (a : G) * ũ * (a : G)⁻¹ * (ũ : G)⁻¹ = ⁅(ũ : G), (a : G)⁆⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.inv_mem _ h1
    have h1 := Subgroup.commutator_mem_commutator hdc hbY
    rw [hYq, Subgroup.mem_bot, commutatorElement_def] at h1
    have key : (b : G) * ((a : G) * ũ * (a : G)⁻¹ * (ũ : G)⁻¹) * (b : G)⁻¹ *
        ((a : G) * ũ * (a : G)⁻¹ * (ũ : G)⁻¹)⁻¹ = 1 := by
      rw [show (b : G) * ((a : G) * ũ * (a : G)⁻¹ * (ũ : G)⁻¹) * (b : G)⁻¹ *
          ((a : G) * ũ * (a : G)⁻¹ * (ũ : G)⁻¹)⁻¹ =
          ((a : G) * ũ * (a : G)⁻¹ * (ũ : G)⁻¹ * b * ((a : G) * ũ * (a : G)⁻¹ * (ũ : G)⁻¹)⁻¹ *
            (b : G)⁻¹)⁻¹ by group, h1, inv_one]
    have htriv : hsV.act b (hsV.act a u * (↑u)⁻¹) * (hsV.act a u * (↑u)⁻¹)⁻¹ = 1 := by
      rw [← hũ, SecHyp.act_secMk, ← map_inv, ← map_mul, SecHyp.act_secMk, ← map_inv,
        ← map_mul, A6Mod.secMk_eq_one_iff]
      have e : ((Setup.rho (conjClosure S.V3 H) H hsV.hHX b
          (Setup.rho (conjClosure S.V3 H) H hsV.hHX a ũ * ũ⁻¹) *
          (Setup.rho (conjClosure S.V3 H) H hsV.hHX a ũ * ũ⁻¹)⁻¹ : ↥(conjClosure S.V3 H)) : G) =
          (b : G) * ((a : G) * ũ * (a : G)⁻¹ * (ũ : G)⁻¹) * (b : G)⁻¹ *
            ((a : G) * ũ * (a : G)⁻¹ * (ũ : G)⁻¹)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe]
      rw [e, key]
      exact (fsuV1 T V).one_mem
    have h0 : (⟨hsV.act b (hsV.act a u * (↑u)⁻¹) * (hsV.act a u * (↑u)⁻¹)⁻¹, hU _⟩ :
        ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))) = 1 := Subtype.ext htriv
    rw [h0, map_one] at hd₂
    exact hq (congrArg Subtype.val
      (A7F.mk7_injective (hd₂.symm.trans (map_one (QuotientGroup.mk' _)).symm)))

end DK

end Setting4

end CFSG.Quasithin.H13.A6
