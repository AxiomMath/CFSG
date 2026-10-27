module

public import CFSG.Quasithin.Vol2.Ch3Sec3Close
public import CFSG.Quasithin.Vol2.Ch3Sec3CloseModel
public import CFSG.Quasithin.Vol2.Ch3Sec3A6Rho

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open A6Coc S6Syl CloseModel
open scoped IsMulCommutative

namespace CloseA

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

theorem inspClose_a
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hA6 : IsAltBlockType L 6) (hTC : tC L T = ⊥)
    (hQV : qL L T = vPlus L T)
    (hIrr : ∃ _ : IsMulCommutative ↥(vPlus L T),
      XMod.IsIrrSec ↥(autOn L (vPlus L T)) (⊥ : Subgroup ↥(vPlus L T)) ⊤)
    (φ : ↥(autOn (L ⊔ T) (vPlus L T)) ≃* Equiv.Perm (Fin 6))
    (hφT : ((autOn T (vPlus L T)).subgroupOf (autOn (L ⊔ T) (vPlus L T))).map φ.toMonoidHom =
      sylowS6) :
    (∀ B : Subgroup G, B ≤ preimageA2 T L φ → IsElemAbelian 2 B →
      Nat.card ↥B ≤ Nat.card ↥(qL L T)) ∧
    (∀ B : Subgroup G, IsMaxElemAbelian (preimageA2 T L φ) B → ¬ B ≤ qL L T →
      ∃ b ∈ B, qL L T ⊓ Subgroup.centralizer (B : Set G) =
        qL L T ⊓ Subgroup.centralizer ({b} : Set G)) ∧
    ∀ B B' : Subgroup G, IsMaxElemAbelian (preimageA2 T L φ) B →
      IsMaxElemAbelian (preimageA2 T L φ) B' → ¬ B ≤ qL L T → ¬ B' ≤ qL L T →
      Nat.card ↥(B ⊔ qL L T) = Nat.card ↥(B' ⊔ qL L T) → B ⊔ qL L T = B' ⊔ qL L T := by
  obtain ⟨hVab, hIrr⟩ := hIrr
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hQT : qL L T ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hOQ : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hUQ : blockU L ≤ qL L T := (C1.blockU_le_blockQ hA6.1).trans hOQ
  have hZ : blockZ L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : z ∈ tC L T := ⟨hQT (hUQ hz.1), hz.2⟩
    rw [hTC] at hz'
    exact hz'
  have hU16 := A6Block.card_blockU_of_blockZ_eq_bot hA6 hZ
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
  have hUV : blockU L = vPlus L T := by
    refine le_antisymm (hQV ▸ hUQ) ?_
    have hinv : XMod.IsInv ↥(autOn L (vPlus L T)) ((blockU L).subgroupOf (vPlus L T)) := by
      rintro ⟨a, ha⟩ v hv
      obtain ⟨g, hgL, rfl⟩ := (CFSG.QuasithinUnique.Setup.mem_autOn_iff).mp ha
      rw [Subgroup.mem_subgroupOf] at hv ⊢
      show (g : G) * v * (g : G)⁻¹ ∈ blockU L
      exact (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (Subgroup.le_normalizer hgL))
        _).mp hv
    rcases hIrr.2 _ hinv bot_le le_top with hb | ht
    · exfalso
      have hle : blockU L ≤ vPlus L T := hQV ▸ hUQ
      have : (blockU L).subgroupOf (vPlus L T) = ⊥ := hb
      rw [Subgroup.subgroupOf_eq_bot] at this
      rw [Subgroup.disjoint_def] at this
      have hc : Nat.card ↥(blockU L) = 1 := by
        rw [Subgroup.card_eq_one, eq_bot_iff]
        intro x hx
        exact this hx (hle hx)
      omega
    · intro v hv
      have : (⟨v, hv⟩ : ↥(vPlus L T)) ∈ (blockU L).subgroupOf (vPlus L T) := ht ▸ Subgroup.mem_top _
      exact this
  obtain ⟨-, α, hAw⟩ := hA6
  have hA : IsAltBlockTypeWith L 6 α := hAw
  obtain ⟨hαs, hαk, β, hβs, hβk, hβe⟩ := hAw
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, hZ, Subgroup.bot_subgroupOf]
  have hQU : qL L T = blockU L := hQV.trans hUV.symm
  let θ : ↥(qL L T) ≃ AltHeart 6 :=
    ((Equiv.subtypeEquivRight fun x => by rw [hQU]).trans
      (Equiv.ofBijective β ⟨hβinj, hβs⟩)).trans Multiplicative.toAdd
  have hθapp : ∀ (q : ↥(qL L T)) (hq : (q : G) ∈ blockU L),
      θ q = Multiplicative.toAdd (β ⟨q, hq⟩) := fun _ _ => rfl
  let ρ : ↥T →* Equiv.Perm (Fin 6) := (A6Trans.rho hA).comp (Subgroup.inclusion hTL)
  have hQN : T ≤ Subgroup.normalizer (qL L T : Set G) :=
    le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T))
  have hθ : ∀ (t : ↥T) (q q' : ↥(qL L T)), (q' : G) = t * q * t⁻¹ →
      θ q' = heartAct 6 (ρ t) (θ q) := by
    intro t q q' hq'
    rw [hθapp q (hQU ▸ q.2), hθapp q' (hQU ▸ q'.2)]
    exact A6Trans.rho_heart hA hβs hβk hβe (Subgroup.inclusion hTL t) ⟨q, hQU ▸ q.2⟩
      ⟨q', hQU ▸ q'.2⟩ hq'
  have hQab : ∀ a ∈ qL L T, ∀ b ∈ qL L T, a * b = b * a := fun a ha b hb => by
    rw [hQV] at ha hb
    exact setLike_mul_comm ha hb
  have hker : ∀ t : ↥T, ρ t = 1 ↔ (t : G) ∈ qL L T := by
    intro t
    constructor
    · intro h1
      have hcv : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = qL L T :=
        (h.centralizer_vPlus h38 h39).2.1
      rw [← hcv]
      refine ⟨t.2, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have hvQ : v ∈ qL L T := hQV ▸ hv
      have hv' : (t : G) * v * (t : G)⁻¹ ∈ qL L T :=
        (Subgroup.mem_normalizer_iff.mp (hQN t.2) v).mp hvQ
      have h2 := hθ t ⟨v, hvQ⟩ ⟨_, hv'⟩ rfl
      rw [h1, heartAct_one] at h2
      have h3 : (t : G) * v * (t : G)⁻¹ = v := congrArg Subtype.val (θ.injective h2)
      calc v * (t : G) = (t : G) * v * (t : G)⁻¹ * t := by rw [h3]
        _ = t * v := by group
    · intro ht
      symm
      apply A6Coc.eq_of_heartAct_eq
      intro w
      rw [heartAct_one]
      obtain ⟨q, rfl⟩ := θ.surjective w
      have hq' : (t : G) * q * (t : G)⁻¹ ∈ qL L T :=
        (Subgroup.mem_normalizer_iff.mp (hQN t.2) q).mp q.2
      have h2 := hθ t q ⟨_, hq'⟩ rfl
      have h3 : (⟨_, hq'⟩ : ↥(qL L T)) = q := Subtype.ext (by
        show (t : G) * q * (t : G)⁻¹ = q
        rw [hQab _ ht _ q.2, mul_inv_cancel_right])
      rw [h3] at h2
      exact h2
  let Dm : Model T (qL L T) := ⟨ρ, θ, hQT, hQN, hker, hθ⟩
  have hQe : IsElemAbelian 2 (qL L T) := by rw [hQV]; exact hred.2.1
  have hT₀T : preimageA2 T L φ ≤ T := inf_le_left
  have hVN : vPlus L T ≤ Subgroup.normalizer (vPlus L T : Set G) := Subgroup.le_normalizer
  have hQT₀ : qL L T ≤ preimageA2 T L φ := by
    intro q hq
    refine ⟨hQT hq, ⟨q, hVN (hQV ▸ hq)⟩, ?_, rfl⟩
    have h1 : conjAct (vPlus L T) ⟨q, hVN (hQV ▸ hq)⟩ = 1 := by
      ext v
      show (q : G) * v * q⁻¹ = v
      have hvQ : (v : G) ∈ qL L T := by rw [hQV]; exact v.2
      rw [hQab q hq v hvQ, mul_inv_cancel_right]
    show conjAct (vPlus L T) ⟨q, hVN (hQV ▸ hq)⟩ ∈
      (aBar2.map φ.symm.toMonoidHom).map (autOn (L ⊔ T) (vPlus L T)).subtype
    rw [h1]
    exact Subgroup.one_mem _
  have hcv : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = qL L T :=
    (h.centralizer_vPlus h38 h39).2.1
  have hTV : T ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_right.trans hred.2.2.2.1
  have hcardT : Nat.card (Dm.img T) = 16 := by
    rw [← Dm.relIndex_eq le_rfl]
    have hk : (InternalSec.autOnHom hTV).ker = (qL L T).subgroupOf T := by
      ext t
      rw [InternalSec.mem_ker_autOnHom, Subgroup.mem_subgroupOf, ← hcv]
      exact ⟨fun hc => ⟨t.2, hc⟩, fun hq => hq.2⟩
    have h1 : (qL L T).relIndex T = Nat.card (autOn T (vPlus L T)) := by
      rw [Subgroup.relIndex, ← hk, Subgroup.index_ker,
        MonoidHom.range_eq_top.mpr (InternalSec.autOnHom_surjective hTV), Subgroup.card_top]
    have hle : autOn T (vPlus L T) ≤ autOn (L ⊔ T) (vPlus L T) :=
      InternalSec.autOn_le_autOn_of_le le_sup_right
    have h2 : Nat.card (autOn T (vPlus L T)) = Nat.card sylowS6 := by
      rw [← hφT, Subgroup.card_map_of_injective φ.injective,
        ← Subgroup.card_subtype (autOn (L ⊔ T) (vPlus L T)) ((autOn T (vPlus L T)).subgroupOf _),
        Subgroup.map_subgroupOf_eq_of_le hle]
    rw [h1, h2, card_sylowS6]
  obtain ⟨g₀, hg₀⟩ := exists_conj_eq_sylowS6 hcardT
  have hcent : ∀ t : ↥T, (t : G) ∈ preimageA2 T L φ → ∀ s : ↥T, ρ t * ρ s = ρ s * ρ t := by
    intro t ht s
    obtain ⟨-, y, hyA, hyt⟩ := ht
    have hyt' : (y : G) = t := hyt
    obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := hyA
    have hsN : (s : G) ∈ Subgroup.normalizer (vPlus L T : Set G) := hTV s.2
    have hbs : conjAct (vPlus L T) ⟨s, hsN⟩ ∈ autOn (L ⊔ T) (vPlus L T) :=
      (CFSG.QuasithinUnique.Setup.mem_autOn_iff).mpr ⟨⟨s, hsN⟩, Subgroup.mem_sup_right s.2, rfl⟩
    have hbsT : (⟨_, hbs⟩ : ↥(autOn (L ⊔ T) (vPlus L T))) ∈
        (autOn T (vPlus L T)).subgroupOf (autOn (L ⊔ T) (vPlus L T)) := by
      rw [Subgroup.mem_subgroupOf]
      exact (CFSG.QuasithinUnique.Setup.mem_autOn_iff).mpr ⟨⟨s, hsN⟩, s.2, rfl⟩
    have hφs : φ ⟨_, hbs⟩ ∈ sylowS6 := hφT ▸ ⟨_, hbsT, rfl⟩
    have hca : a * φ ⟨_, hbs⟩ = φ ⟨_, hbs⟩ * a := ((mem_center_iff a).mpr ha).2 _ hφs
    have hcb : φ.symm a * ⟨_, hbs⟩ = ⟨_, hbs⟩ * φ.symm a := by
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hca]
    have hcb' : conjAct (vPlus L T) y * conjAct (vPlus L T) ⟨s, hsN⟩ =
        conjAct (vPlus L T) ⟨s, hsN⟩ * conjAct (vPlus L T) y := by
      have := congrArg Subtype.val hcb
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at this
      rw [← hb]
      exact this
    have hc1 : conjAct (vPlus L T) (y * ⟨s, hsN⟩ * y⁻¹ * (⟨s, hsN⟩)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcb']
      group
    have hcC := Lem3328.mem_centralizer_of_conjAct_eq_one _ hc1
    have hcT : t * s * t⁻¹ * s⁻¹ ∈ (qL L T).subgroupOf T := by
      rw [Subgroup.mem_subgroupOf, ← hcv]
      refine ⟨(t * s * t⁻¹ * s⁻¹).2, ?_⟩
      have e : ((t * s * t⁻¹ * s⁻¹ : ↥T) : G) =
          ((y * ⟨s, hsN⟩ * y⁻¹ * (⟨s, hsN⟩)⁻¹ :
            ↥(Subgroup.normalizer (vPlus L T : Set G))) : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hyt']
      rw [e]
      exact hcC
    have h1 : ρ (t * s * t⁻¹ * s⁻¹) = 1 := (hker _).mpr (Subgroup.mem_subgroupOf.mp hcT)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc ρ t * ρ s = ρ t * ρ s * (ρ t)⁻¹ * (ρ s)⁻¹ * (ρ s * ρ t) := by group
      _ = ρ s * ρ t := by rw [h1, one_mul]
  have himg : ∀ t : ↥T, (t : G) ∈ preimageA2 T L φ → g₀⁻¹ * ρ t * g₀⁻¹⁻¹ ∈ aBar2 := by
    intro t ht
    rw [← mem_center_iff]
    have hmemS : ∀ σ ∈ Dm.img T, g₀⁻¹ * σ * g₀⁻¹⁻¹ ∈ sylowS6 := by
      intro σ hσ
      rw [hg₀] at hσ
      obtain ⟨τ, hτ, rfl⟩ := hσ
      have e : g₀⁻¹ * ((MulAut.conj g₀).toMonoidHom τ) * g₀⁻¹⁻¹ = τ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact hτ
    refine ⟨hmemS _ (Dm.mem_img.mpr ⟨t, t.2, rfl⟩), fun z hz => ?_⟩
    have hz' : g₀ * z * g₀⁻¹ ∈ Dm.img T := by
      rw [hg₀]
      exact ⟨z, hz, rfl⟩
    obtain ⟨s, -, hs⟩ := Dm.mem_img.mp hz'
    have hs' : ρ s = g₀ * z * g₀⁻¹ := hs
    have e : z = g₀⁻¹ * ρ s * g₀⁻¹⁻¹ := by
      rw [hs']
      group
    rw [e]
    have hts := hcent t ht s
    calc g₀⁻¹ * ρ t * g₀⁻¹⁻¹ * (g₀⁻¹ * ρ s * g₀⁻¹⁻¹) =
        g₀⁻¹ * (ρ t * ρ s) * g₀⁻¹⁻¹ := by group
      _ = g₀⁻¹ * (ρ s * ρ t) * g₀⁻¹⁻¹ := by rw [hts]
      _ = g₀⁻¹ * ρ s * g₀⁻¹⁻¹ * (g₀⁻¹ * ρ t * g₀⁻¹⁻¹) := by group
  exact Dm.offenders hQe hQT₀ hT₀T himg

end CloseA

end CFSG.Quasithin.H13
