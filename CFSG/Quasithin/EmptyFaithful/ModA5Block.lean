module

public import CFSG.Quasithin.EmptyFaithful.S153F19
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv CFSG.Open
open scoped Pointwise commutatorElement

namespace ModA5

private def v4set : Finset (Perm (Fin 5)) :=
  {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2}

private theorem v4set_one : (1 : Perm (Fin 5)) ∈ v4set := by decide +kernel

private theorem v4set_mul : ∀ a ∈ v4set, ∀ b ∈ v4set, a * b ∈ v4set := by decide +kernel

private theorem v4set_inv : ∀ a ∈ v4set, a⁻¹ ∈ v4set := by decide +kernel

private theorem v4set_alt : ∀ a ∈ v4set, Perm.sign a = 1 := by decide +kernel

private def v4 : Subgroup Alt5 where
  carrier := {x | (x : Perm (Fin 5)) ∈ v4set}
  mul_mem' := fun {a b} ha hb => v4set_mul a ha b hb
  one_mem' := v4set_one
  inv_mem' := fun {a} ha => v4set_inv a ha

private theorem v4_card : Nat.card v4 = 4 := by
  show Nat.card {x : Alt5 // (x : Perm (Fin 5)) ∈ v4set} = 4
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

private def NormV4 (σ : Perm (Fin 5)) : Prop := ∀ x ∈ v4set, σ * x * σ⁻¹ ∈ v4set

private instance (σ : Perm (Fin 5)) : Decidable (NormV4 σ) := by
  unfold NormV4; infer_instance

private def FixV4 (v : Fin 5 → ZMod 2) : Prop := ∀ x ∈ v4set, pact x v = v

private instance (v : Fin 5 → ZMod 2) : Decidable (FixV4 v) := by
  unfold FixV4; infer_instance

private theorem fixed_of_normV4 :
    ∀ σ : Perm (Fin 5), NormV4 σ → ∀ v : Fin 5 → ZMod 2, isEven v → FixV4 v → pact σ v = v := by
  decide +kernel

private theorem exists_conj_v4 (Q : Subgroup Alt5) (hQ : Nat.card Q = 4) :
    ∃ g : Alt5, ∀ x : Alt5, x ∈ Q ↔ g⁻¹ * x * g ∈ v4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : (Nat.card Alt5).factorization 2 = 2 := by
    rw [a5_card]; decide +kernel
  let PQ : Sylow 2 Alt5 := Sylow.ofCard Q (by rw [hQ, hf]; norm_num)
  let PV : Sylow 2 Alt5 := Sylow.ofCard v4 (by rw [v4_card, hf]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Alt5 PV PQ
  refine ⟨g, fun x => ?_⟩
  have h1 : ((g • PV : Sylow 2 Alt5) : Subgroup Alt5) = (PQ : Subgroup Alt5) := by rw [hg]
  rw [Sylow.coe_subgroup_smul] at h1
  have e : (x ∈ (PQ : Subgroup Alt5)) ↔ x ∈ MulAut.conj g • (PV : Subgroup Alt5) := by rw [← h1]
  have hPQ : (PQ : Subgroup Alt5) = Q := Sylow.coe_ofCard _ _
  have hPV : (PV : Subgroup Alt5) = v4 := Sylow.coe_ofCard _ _
  rw [hPQ, hPV, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at e
  rw [e]
  simp [mul_assoc]

private theorem vact_eq_of_normalizes (Q : Subgroup Alt5) (hQ : Nat.card Q = 4) (σ : Alt5)
    (hσ : ∀ q ∈ Q, σ * q * σ⁻¹ ∈ Q) (w : evenWeight 5)
    (hw : ∀ q ∈ Q, vact (q : Perm (Fin 5)) w = w) : vact (σ : Perm (Fin 5)) w = w := by
  obtain ⟨g, hg⟩ := exists_conj_v4 Q hQ
  have hconj : ∀ x : Alt5, x ∈ v4 → g * x * g⁻¹ ∈ Q := fun x hx =>
    (hg _).mpr (by simpa [mul_assoc] using hx)
  have hN : NormV4 ((g⁻¹ * σ * g : Alt5) : Perm (Fin 5)) := by
    intro x hx
    have hxa : x ∈ alternatingGroup (Fin 5) := Perm.mem_alternatingGroup.mpr (v4set_alt x hx)
    have hxv : (⟨x, hxa⟩ : Alt5) ∈ v4 := hx
    have h2 := hσ _ (hconj _ hxv)
    have h3 := (hg _).mp h2
    have e : g⁻¹ * (σ * (g * ⟨x, hxa⟩ * g⁻¹) * σ⁻¹) * g =
        (g⁻¹ * σ * g) * ⟨x, hxa⟩ * (g⁻¹ * σ * g)⁻¹ := by group
    rw [e] at h3
    exact h3
  have hF : FixV4 (pact (g⁻¹ : Alt5) w.1) := by
    intro x hx
    have hxa : x ∈ alternatingGroup (Fin 5) := Perm.mem_alternatingGroup.mpr (v4set_alt x hx)
    have hxv : (⟨x, hxa⟩ : Alt5) ∈ v4 := hx
    have h2 := hw _ (hconj _ hxv)
    have h2' : pact ((g * ⟨x, hxa⟩ * g⁻¹ : Alt5) : Perm (Fin 5)) w.1 = w.1 :=
      congrArg Subtype.val h2
    calc pact x (pact (g⁻¹ : Alt5) w.1) = pact (x * (g⁻¹ : Alt5)) w.1 := (pact_mul _ _ _).symm
      _ = pact ((g⁻¹ : Alt5) * ((g * ⟨x, hxa⟩ * g⁻¹ : Alt5) : Perm (Fin 5))) w.1 := by
          congr 1
          simp [mul_assoc]
      _ = pact (g⁻¹ : Alt5) (pact ((g * ⟨x, hxa⟩ * g⁻¹ : Alt5) : Perm (Fin 5)) w.1) :=
          pact_mul _ _ _
      _ = pact (g⁻¹ : Alt5) w.1 := by rw [h2']
  have hE : isEven (pact (g⁻¹ : Alt5) w.1) := pact_mem _ w.2
  have key := fixed_of_normV4 _ hN _ hE hF
  have key' : pact ((g⁻¹ * σ : Alt5) : Perm (Fin 5)) w.1 = pact (g⁻¹ : Alt5) w.1 := by
    rw [show (((g⁻¹ * σ : Alt5)) : Perm (Fin 5)) = ((g⁻¹ * σ * g : Alt5) : Perm (Fin 5)) *
      (g⁻¹ : Alt5) by simp [mul_assoc], pact_mul]
    exact key
  have key'' : pact (g⁻¹ : Alt5) (pact (σ : Perm (Fin 5)) w.1) = pact (g⁻¹ : Alt5) w.1 := by
    rw [← pact_mul]
    exact key'
  have hgg : ∀ x : Fin 5 → ZMod 2,
      pact (g : Perm (Fin 5)) (pact ((g⁻¹ : Alt5) : Perm (Fin 5)) x) = x := by
    intro x
    rw [← pact_mul]
    have e : (g : Perm (Fin 5)) * ((g⁻¹ : Alt5) : Perm (Fin 5)) = 1 := by simp
    rw [e, pact_one]
  have h4 := congrArg (pact (g : Perm (Fin 5))) key''
  rw [hgg, hgg] at h4
  exact Subtype.ext h4

section Block

variable {G : Type} [Group G]

private theorem mem_pCore_iff_mem_blockQ' {L : Subgroup G} (x : ↥L) :
    x ∈ CFSG.pCore 2 L ↔ (x : G) ∈ blockQ L := by
  show x ∈ CFSG.pCore 2 L ↔ (x : G) ∈ pCoreOf 2 L
  unfold pCoreOf
  exact (Subgroup.mem_map_iff_mem L.subtype_injective).symm

private theorem blockU_le_blockQ' [Finite G] (L : Subgroup G) : blockU L ≤ blockQ L := by
  rw [blockU, Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have h := (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockQ L hg₂) g₁⁻¹).mp
    (inv_mem hg₁)
  have e : ⁅g₁, g₂⁆ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by
    rw [commutatorElement_def]; group
  rw [e]
  exact mul_mem hg₁ h

private theorem toAdd_beta_conj {L : Subgroup G} {α : ↥L →* Alt5}
    {β : ↥(blockU L) →* Multiplicative (evenWeight 5)}
    (hβe : ∀ ℓ : ↥L, ∀ u v : ↥(blockU L), (v : G) = ℓ * u * ℓ⁻¹ → ∀ i : Fin 5,
      ((Multiplicative.toAdd (β v) : evenWeight 5) : Fin 5 → ZMod 2) i =
        ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2)
          ((α ℓ : Equiv.Perm (Fin 5))⁻¹ i))
    (ℓ : ↥L) (u v : ↥(blockU L)) (h : (v : G) = ℓ * u * ℓ⁻¹) :
    Multiplicative.toAdd (β v) = vact (α ℓ : Perm (Fin 5)) (Multiplicative.toAdd (β u)) :=
  Subtype.ext (funext fun i => hβe ℓ u v h i)

end Block

end ModA5

theorem a5FixedPoints_holds : A5FixedPoints := by
  intro G _ _ L P hL hP y hyL hyN hodd
  obtain ⟨α, hα, -, β, hβ, hβk, hβe⟩ := hL
  have hUQ : blockU L ≤ blockQ L := ModA5.blockU_le_blockQ' L
  have hyU : y ∈ Subgroup.normalizer (blockU L : Set G) := C1.le_normalizer_blockU L hyL
  have hQ2 : IsPGroup 2 (P.subgroupOf L |>.map α) := (hP.2.1.comap_subtype (K := L)).map α
  have hQidx : ¬ 2 ∣ (P.subgroupOf L |>.map α).index := fun h =>
    hP.2.2 (h.trans (Subgroup.index_map_dvd _ hα))
  have hQcard : Nat.card (P.subgroupOf L |>.map α) = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hQ2.exists_card_eq
    have h60 : (P.subgroupOf L |>.map α).index * 2 ^ k = 60 := by
      rw [← hk, Subgroup.index_mul_card, a5_card]
    have hk2 : k = 2 := by
      rcases k with _ | _ | _ | k
      · omega
      · omega
      · rfl
      · exfalso
        have h8 : (8 : ℕ) ∣ 60 := by
          refine ⟨(P.subgroupOf L |>.map α).index * 2 ^ k, ?_⟩
          rw [← h60]
          ring
        omega
    rw [hk, hk2]
    norm_num
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxU : x ∈ blockU L := hx.1
  have hxPc : ∀ p ∈ P, p * x = x * p := Subgroup.mem_centralizer_iff.mp hx.2
  have hyxU : y * x * y⁻¹ ∈ blockU L := (Subgroup.mem_normalizer_iff.mp hyU x).mp hxU
  let u : ↥(blockU L) := ⟨x, hxU⟩
  let v : ↥(blockU L) := ⟨y * x * y⁻¹, hyxU⟩
  let ℓ : ↥L := ⟨y, hyL⟩
  have hwQ : ∀ q ∈ (P.subgroupOf L |>.map α),
      vact (q : Perm (Fin 5)) (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β u) := by
    intro q hq
    obtain ⟨p', hp', rfl⟩ := Subgroup.mem_map.mp hq
    have hpP : (p' : G) ∈ P := hp'
    have hv : ((u : ↥(blockU L)) : G) = (p' : G) * (u : G) * (p' : G)⁻¹ := by
      show x = (p' : G) * x * (p' : G)⁻¹
      rw [hxPc _ hpP]; group
    exact (ModA5.toAdd_beta_conj hβe p' u u hv).symm
  have hσ : ∀ q ∈ (P.subgroupOf L |>.map α), α ℓ * q * (α ℓ)⁻¹ ∈ (P.subgroupOf L |>.map α) := by
    intro q hq
    obtain ⟨p', hp', rfl⟩ := Subgroup.mem_map.mp hq
    refine Subgroup.mem_map.mpr ⟨ℓ * p' * ℓ⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have hpP : (p' : G) ∈ P := hp'
    have h := (Subgroup.mem_normalizer_iff.mp hyN (p' : G)).mp hpP
    exact h
  have hfix := ModA5.vact_eq_of_normalizes _ hQcard (α ℓ) hσ _ hwQ
  have hβv : β v = β u := by
    have h1 := ModA5.toAdd_beta_conj hβe ℓ u v rfl
    exact Multiplicative.toAdd.injective (h1.trans hfix)
  have hcZ : y * x * y⁻¹ * x⁻¹ ∈ blockZ L := by
    have h : v * u⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hβv, mul_inv_cancel]
    rw [hβk] at h
    exact Subgroup.mem_subgroupOf.mp h
  obtain ⟨c, hc⟩ : ∃ c : G, c = y * x * y⁻¹ * x⁻¹ := ⟨_, rfl⟩
  rw [← hc] at hcZ
  have hyc : y * c = c * y := Subgroup.mem_centralizer_iff.mp hcZ.2 y hyL
  have hcx : y * x * y⁻¹ = c * x := by rw [hc]; group
  have hiter : ∀ k : ℕ, y ^ k * x * (y ^ k)⁻¹ = c ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hcomm : y * c ^ k = c ^ k * y := (Commute.pow_right (show Commute y c from hyc) k).eq
      have e1 : y * c ^ k * y⁻¹ = c ^ k := by rw [hcomm]; group
      calc y ^ (k + 1) * x * (y ^ (k + 1))⁻¹
          = y * (y ^ k * x * (y ^ k)⁻¹) * y⁻¹ := by group
        _ = y * (c ^ k * x) * y⁻¹ := by rw [ih]
        _ = (y * c ^ k * y⁻¹) * (y * x * y⁻¹) := by group
        _ = c ^ (k + 1) * x := by rw [e1, hcx, pow_succ, mul_assoc]
  have hm : c ^ orderOf y = 1 := by
    have h := hiter (orderOf y)
    rw [pow_orderOf_eq_one, inv_one, mul_one, one_mul] at h
    exact mul_eq_right.mp h.symm
  obtain ⟨a, ha⟩ := C1.exists_pow_eq_one_of_isPGroup (C1.blockQ_isPGroup L) (hUQ hcZ.1)
  have hcop : Nat.Coprime (orderOf y) (2 ^ a) :=
    Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hodd)
  have hc1 : c = 1 := by
    have h1 : orderOf c = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hm) hcop)
        (orderOf_dvd_of_pow_eq_one ha)
    exact orderOf_eq_one_iff.mp h1
  rw [hc1, one_mul] at hcx
  calc x * y = (y * x * y⁻¹) * y := by rw [hcx]
    _ = y * x := by group

theorem a5OddCommuting_holds : A5OddCommuting := by
  intro G _ _ L hL hZ y hyN _ hcomm
  obtain ⟨α, hα, hαk, β, hβ, hβk, hβe⟩ := hL
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, hZ, Subgroup.bot_subgroupOf]
  have hyU : y ∈ Subgroup.normalizer (blockU L : Set G) := C1.mem_normalizer_blockU hyN
  have hyU' : ∀ u : ↥(blockU L), y * (u : G) * y⁻¹ ∈ blockU L := fun u =>
    (Subgroup.mem_normalizer_iff.mp hyU u).mp u.2
  let φ : ↥(blockU L) →* ↥(blockU L) :=
    { toFun := fun u => ⟨y * (u : G) * y⁻¹, hyU' u⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        show y * ((a : G) * (b : G)) * y⁻¹ = y * (a : G) * y⁻¹ * (y * (b : G) * y⁻¹)
        group }
  have hφinj : Function.Injective φ := by
    intro a b h
    apply Subtype.ext
    have h' : y * (a : G) * y⁻¹ = y * (b : G) * y⁻¹ := congrArg Subtype.val h
    simpa using h'
  let βe : ↥(blockU L) ≃* Multiplicative (evenWeight 5) := MulEquiv.ofBijective β ⟨hinj, hβ⟩
  let gM : Multiplicative (evenWeight 5) →* Multiplicative (evenWeight 5) :=
    β.comp (φ.comp βe.symm.toMonoidHom)
  have hgMinj : Function.Injective gM := hinj.comp (hφinj.comp βe.symm.injective)
  let g : evenWeight 5 → evenWeight 5 := fun w => Multiplicative.toAdd (gM (Multiplicative.ofAdd w))
  have hadd : ∀ a b, g (a + b) = g a + g b := by
    intro a b
    simp only [g, ofAdd_add, map_mul, toAdd_mul]
  have hginj : Function.Injective g := by
    intro a b h
    exact Multiplicative.ofAdd.injective (hgMinj (Multiplicative.toAdd.injective h))
  have hgcomm : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → ∀ w, g (vact σ w) = vact σ (g w) := by
    intro σ hσ w
    obtain ⟨ℓ, hℓ⟩ := hα ⟨σ, Perm.mem_alternatingGroup.mpr hσ⟩
    have hℓσ : ((α ℓ : Alt5) : Perm (Fin 5)) = σ := by rw [hℓ]
    set u₀ : ↥(blockU L) := βe.symm (Multiplicative.ofAdd w) with hu₀
    have hβu₀ : β u₀ = Multiplicative.ofAdd w := by
      have := βe.apply_symm_apply (Multiplicative.ofAdd w)
      exact this
    have hℓU : (ℓ : G) * (u₀ : G) * (ℓ : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU L ℓ.2) u₀).mp u₀.2
    let v₀ : ↥(blockU L) := ⟨(ℓ : G) * (u₀ : G) * (ℓ : G)⁻¹, hℓU⟩
    have h1 : Multiplicative.toAdd (β v₀) = vact σ w := by
      have := ModA5.toAdd_beta_conj hβe ℓ u₀ v₀ rfl
      rw [hℓσ, hβu₀] at this
      exact this
    have h2 : βe.symm (Multiplicative.ofAdd (vact σ w)) = v₀ := by
      rw [← h1, ofAdd_toAdd]
      exact βe.symm_apply_apply v₀
    have hyL : y * (ℓ : G) * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyN ℓ).mp ℓ.2
    let ℓ' : ↥L := ⟨y * (ℓ : G) * y⁻¹, hyL⟩
    have hαℓ' : α ℓ' = α ℓ := by
      have hq : (ℓ' * ℓ⁻¹ : ↥L) ∈ CFSG.pCore 2 L := by
        rw [ModA5.mem_pCore_iff_mem_blockQ']
        have h := inv_mem (hcomm ℓ ℓ.2)
        have e : ((ℓ' * ℓ⁻¹ : ↥L) : G) = (↑ℓ * y * (↑ℓ)⁻¹ * y⁻¹)⁻¹ := by
          show y * (ℓ : G) * y⁻¹ * (ℓ : G)⁻¹ = _
          group
        rw [e]
        exact h
      rw [← hαk] at hq
      have h0 : α (ℓ' * ℓ⁻¹) = 1 := hq
      rw [map_mul, map_inv, mul_inv_eq_one] at h0
      exact h0
    have h3 : Multiplicative.toAdd (β (φ v₀)) =
        vact σ (Multiplicative.toAdd (β (φ u₀))) := by
      have := ModA5.toAdd_beta_conj hβe ℓ' (φ u₀) (φ v₀) (by
        show y * ((ℓ : G) * (u₀ : G) * (ℓ : G)⁻¹) * y⁻¹ =
          y * (ℓ : G) * y⁻¹ * (y * (u₀ : G) * y⁻¹) * (y * (ℓ : G) * y⁻¹)⁻¹
        group)
      rw [hαℓ', hℓσ] at this
      exact this
    have h4 : g (vact σ w) = Multiplicative.toAdd (β (φ v₀)) := by
      show Multiplicative.toAdd (β (φ (βe.symm (Multiplicative.ofAdd (vact σ w))))) = _
      rw [h2]
    have h5 : g w = Multiplicative.toAdd (β (φ u₀)) := rfl
    rw [h4, h5]
    exact h3
  have hfix := rigid g hadd hginj hgcomm
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' : u ∈ blockU L := hu
  have h1 : g (Multiplicative.toAdd (β ⟨u, hu'⟩)) = Multiplicative.toAdd (β ⟨u, hu'⟩) :=
    hfix _
  have h2 : β (φ ⟨u, hu'⟩) = β ⟨u, hu'⟩ := by
    have h3 : g (Multiplicative.toAdd (β ⟨u, hu'⟩)) = Multiplicative.toAdd (β (φ ⟨u, hu'⟩)) := by
      show Multiplicative.toAdd (β (φ (βe.symm (Multiplicative.ofAdd (Multiplicative.toAdd (β ⟨u, hu'⟩)))))) = _
      rw [ofAdd_toAdd]
      have : βe.symm (β ⟨u, hu'⟩) = ⟨u, hu'⟩ := βe.symm_apply_apply ⟨u, hu'⟩
      rw [this]
    rw [h3] at h1
    exact Multiplicative.toAdd.injective h1
  have h6 : φ ⟨u, hu'⟩ = ⟨u, hu'⟩ := hinj h2
  have h7 : y * u * y⁻¹ = u := congrArg Subtype.val h6
  calc u * y = (y * u * y⁻¹) * y := by rw [h7]
    _ = y * u := by group

end CFSG.Quasithin
