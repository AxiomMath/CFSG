module

public import CFSG.Quasithin.Vol2.Ch3Sec3Close
public import CFSG.Quasithin.Vol2.Ch3Sec3ModelP5
public import CFSG.Quasithin.Vol2.Ch3Sec3P5Quot
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3328

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open S6Syl CloseModelG ModelA2 ModelP5 P5Quot
open scoped IsMulCommutative

namespace CloseB

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

theorem inspClose_b
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hA6 : IsAltBlockType L 6) (hTC : tC L T = ⊥)
    (hb : ∃ _ : IsMulCommutative ↥(qL L T), Nat.card ↥(qL L T) = 2 ^ 5 ∧
      permQuot6Model.Realizes (autOn (L ⊔ T) (qL L T)) ⊤ ⊥)
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
  obtain ⟨hQab', hQ32, π, hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hb
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hQT : qL L T ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hQab : ∀ a ∈ qL L T, ∀ b ∈ qL L T, a * b = b * a := fun a ha b hb =>
    setLike_mul_comm ha hb
  have hcv : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = qL L T :=
    (h.centralizer_vPlus h38 h39).2.1
  have hQN : T ≤ Subgroup.normalizer (qL L T : Set G) :=
    le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T))
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (qL L T : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have hβeq : ∀ (γ : Equiv.Perm (Fin 6)) (u : ↥(⊤ : Subgroup ↥(qL L T))),
      Multiplicative.toAdd (crdHom (β ⟨((π γ : ↥(autOn (L ⊔ T) (qL L T))) : MulAut ↥(qL L T))
        (u : ↥(qL L T)), Subgroup.mem_top _⟩)) =
        P5.act γ (Multiplicative.toAdd (crdHom (β u))) := by
    intro γ u
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have h1 := hβe γ u m (Subgroup.mem_top _) (Subgroup.mem_top _) hm.symm
    rw [h1, ← hm, crdHom_mk, crdHom_mk, P5.act_crd]
    rfl
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβk u).mp hu
    exact Subtype.ext (by rw [Subgroup.mem_bot] at this; exact this)
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply P5.eq_one_of_act
    intro v
    obtain ⟨m, hm⟩ := crdHom_surjective (Multiplicative.ofAdd v)
    obtain ⟨u, rfl⟩ := hβs m
    have h1 := hβeq γ u
    rw [hγ] at h1
    have h2 : (⟨((1 : ↥(autOn (L ⊔ T) (qL L T))) : MulAut ↥(qL L T)) (u : ↥(qL L T)),
        Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥(qL L T))) = u := Subtype.ext rfl
    rw [h2, hm, toAdd_ofAdd] at h1
    exact h1.symm
  let πe : Equiv.Perm (Fin 6) ≃* ↥(autOn (L ⊔ T) (qL L T)) :=
    MulEquiv.ofBijective π ⟨hπinj, hπs⟩
  have hTaut : ∀ t : ↥T, conjAct (qL L T) ⟨t, hQN t.2⟩ ∈ autOn (L ⊔ T) (qL L T) := fun t =>
    (CFSG.QuasithinUnique.Setup.mem_autOn_iff).mpr ⟨⟨t, hQN t.2⟩, Subgroup.mem_sup_right t.2, rfl⟩
  let cT : ↥T →* ↥(autOn (L ⊔ T) (qL L T)) :=
    ((conjAct (qL L T)).comp (Subgroup.inclusion hQN)).codRestrict _ hTaut
  let ρ : ↥T →* Equiv.Perm (Fin 6) := πe.symm.toMonoidHom.comp cT
  have hπρ : ∀ t : ↥T, π (ρ t) = cT t := fun t => πe.apply_symm_apply (cT t)
  let θ : ↥(qL L T) ≃ P5.Vec5 :=
    ((Subgroup.topEquiv.symm.toEquiv.trans (Equiv.ofBijective β ⟨hβinj, hβs⟩)).trans
      (Equiv.ofBijective crdHom ⟨crdHom_injective, crdHom_surjective⟩)).trans
      Multiplicative.toAdd
  have hθ : ∀ (t : ↥T) (q q' : ↥(qL L T)), (q' : G) = t * q * t⁻¹ →
      θ q' = P5.actHom (ρ t) (θ q) := by
    intro t q q' hq'
    have h1 := hβeq (ρ t) ⟨q, Subgroup.mem_top _⟩
    rw [hπρ] at h1
    have h2 : (⟨((cT t : ↥(autOn (L ⊔ T) (qL L T))) : MulAut ↥(qL L T)) q,
        Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥(qL L T))) = ⟨q', Subgroup.mem_top _⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      show (t : G) * q * (t : G)⁻¹ = q'
      exact hq'.symm
    rw [h2] at h1
    exact h1
  have hker : ∀ t : ↥T, ρ t = 1 ↔ (t : G) ∈ qL L T := by
    intro t
    have hiff : ρ t = 1 ↔ cT t = 1 := by
      rw [← hπρ]
      exact ⟨fun h1 => by rw [h1]; exact map_one π, fun h1 => hπinj (h1.trans (map_one π).symm)⟩
    rw [hiff]
    constructor
    · intro h1
      have h2 : conjAct (qL L T) ⟨t, hQN t.2⟩ = 1 := congrArg Subtype.val h1
      have hc := Lem3328.mem_centralizer_of_conjAct_eq_one _ h2
      rw [← hcv]
      exact ⟨t.2, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVQ) hc⟩
    · intro ht
      apply Subtype.ext
      apply InternalSec.conjAct_eq_one_of_mem_centralizer
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact hQab q hq t ht
  let Dm : CloseModelG.Model P5.actHom T (qL L T) := ⟨ρ, θ, hQT, hQN, hker, hθ⟩
  have hQe : IsElemAbelian 2 (qL L T) := by
    have hΦ := h.frattini_qL_le_tC h38 h39 hA6.1 hTL
    rw [hTC] at hΦ
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine Lem3328.isElemAbelian_of_frattini_eq_bot
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) ?_
    rw [eq_bot_iff]
    intro x hx
    have := hΦ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot] at this ⊢
    exact Subtype.ext this
  have hT₀T : preimageA2 T L φ ≤ T := inf_le_left
  have hVN : vPlus L T ≤ Subgroup.normalizer (vPlus L T : Set G) := Subgroup.le_normalizer
  have hTV : T ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_right.trans hred.2.2.2.1
  have hQT₀ : qL L T ≤ preimageA2 T L φ := by
    intro q hq
    refine ⟨hQT hq, ⟨q, hTV (hQT hq)⟩, ?_, rfl⟩
    have h1 : conjAct (vPlus L T) ⟨q, hTV (hQT hq)⟩ = 1 := by
      apply InternalSec.conjAct_eq_one_of_mem_centralizer
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact hQab v (hVQ hv) q hq
    show conjAct (vPlus L T) ⟨q, hTV (hQT hq)⟩ ∈
      (aBar2.map φ.symm.toMonoidHom).map (autOn (L ⊔ T) (vPlus L T)).subtype
    rw [h1]
    exact Subgroup.one_mem _
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
  have hcard : Nat.card ↥(qL L T) = Nat.card P5.Vec5 := by rw [hQ32, card_vec5]; rfl
  exact Dm.offenders hQe hcard wt_le wt_W2
    (fun X X' hX hX' hne hne' heq heq' _ => wt_W3 X X' hX hX' hne hne' heq heq')
    hQT₀ hT₀T himg

end CloseB

end CFSG.Quasithin.H13
