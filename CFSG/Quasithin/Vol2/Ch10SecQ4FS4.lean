module

public import CFSG.Quasithin.Vol2.Ch10SecQ4S2
public import CFSG.Quasithin.Vol2.Ch10SecFH
public import CFSG.Quasithin.Vol2.Ch10SecQ4FS1
public import CFSG.Quasithin.Vol2.Ch10SecQ4S4
public import CFSG.Quasithin.Vol2.Ch10SecQ4S9

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.QuasithinUnique.A5.Delta5

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem le_normalizer_blockU (K : Subgroup G) :
    K ≤ Subgroup.normalizer (blockU K : Set G) := by
  rw [blockU_eq_lit]
  exact CGT.PushingUpLit.le_normalizer_blockU K

omit [Finite G] in
theorem conj_eq_of_mem_blockU {K S : Subgroup G} (hKs : IsShort2 K) (hKa : IsAltType K 5)
    (hP4 : ∀ α : ↥K →* alternatingGroup (Fin 5), Function.Surjective α →
      α.ker = CFSG.pCore 2 ↥K → Nat.card ↥((S.subgroupOf K).map α) = 4)
    {q : G} (hqK : q ∈ K) (hq3 : q ^ 3 = 1)
    (hqN : q ∈ Subgroup.normalizer (S : Set G)) {u : G} (hu : u ∈ blockU K)
    (huS : ∀ s ∈ S, s * u = u * s) : q * u * q⁻¹ = u := by
  obtain ⟨α, hαs, hαk, β, -, hβk, hβe⟩ := hKa
  have hP4' := hP4 α hαs hαk
  obtain ⟨a, haP, b, hbP, haa, hbb, hab, ha1, hb1, hne, -⟩ := exists_pair_of_card_four hP4'
  have hcard := card_fixSet_pair_le a b a.2 b.2 (congrArg Subtype.val haa)
    (congrArg Subtype.val hbb) (fun h => ha1 (Subtype.ext h)) (fun h => hb1 (Subtype.ext h))
    (fun h => hne (Subtype.ext h)) (congrArg Subtype.val hab)
  have hfix : ∀ (v : G) (hv : v ∈ blockU K), (∀ s ∈ S, s * v = v * s) →
      ((Multiplicative.toAdd (β ⟨v, hv⟩) : evenWeight 5) : Fin 5 → ZMod 2) ∈ fixSet₂ a b := by
    intro v hv hvS
    have hpf : ∀ p ∈ (S.subgroupOf K).map α, pact (p : Equiv.Perm (Fin 5))
        ((Multiplicative.toAdd (β ⟨v, hv⟩) : evenWeight 5) : Fin 5 → ZMod 2) =
        ((Multiplicative.toAdd (β ⟨v, hv⟩) : evenWeight 5) : Fin 5 → ZMod 2) := by
      rintro _ ⟨x, hx, rfl⟩
      have hxv : v = (x : G) * v * (x : G)⁻¹ := by
        rw [hvS x (Subgroup.mem_subgroupOf.mp hx), mul_inv_cancel_right]
      funext i
      exact (hβe x ⟨v, hv⟩ ⟨v, hv⟩ hxv i).symm
    exact mem_fixSet₂.mpr ⟨(Multiplicative.toAdd (β ⟨v, hv⟩)).2, hpf a haP, hpf b hbP⟩
  have hquU : q * u * q⁻¹ ∈ blockU K :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_blockU K hqK) u).mp hu
  have hquS : ∀ s ∈ S, s * (q * u * q⁻¹) = (q * u * q⁻¹) * s := by
    intro s hs
    have h1 : q⁻¹ * s * q ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hqN) s).mp hs
      simpa using this
    have h2 := huS _ h1
    calc s * (q * u * q⁻¹) = q * ((q⁻¹ * s * q) * u) * q⁻¹ := by group
      _ = q * (u * (q⁻¹ * s * q)) * q⁻¹ := by rw [h2]
      _ = (q * u * q⁻¹) * s := by group
  have hZ : ∀ (v : G) (hv : v ∈ blockU K), β ⟨v, hv⟩ = 1 → v ∈ Subgroup.centralizer (K : Set G) :=
    fun v hv h1 => by
      have h3 : (⟨v, hv⟩ : ↥(blockU K)) ∈ β.ker := h1
      rw [hβk, Subgroup.mem_subgroupOf] at h3
      exact h3.2
  by_cases h0 : β ⟨u, hu⟩ = 1
  · have := Subgroup.mem_centralizer_iff.mp (hZ u hu h0) q hqK
    rw [this, mul_inv_cancel_right]
  · have h0' : β ⟨q * u * q⁻¹, hquU⟩ ≠ 1 := by
      intro h1
      apply h0
      have hw := hZ _ hquU h1
      have hcq := Subgroup.mem_centralizer_iff.mp hw q hqK
      have huw : q * u * q⁻¹ = u := by
        apply mul_left_cancel (a := q)
        rw [hcq, inv_mul_cancel_right]
      have hmem : u ∈ blockZ K := ⟨hu, huw ▸ hw⟩
      have : (⟨u, hu⟩ : ↥(blockU K)) ∈ β.ker := by
        rw [hβk, Subgroup.mem_subgroupOf]
        exact hmem
      exact this
    have hx := hfix u hu huS
    have hy := hfix _ hquU hquS
    have hval : ∀ {w : Multiplicative ↥(evenWeight 5)}, w ≠ 1 →
        ((Multiplicative.toAdd w : evenWeight 5) : Fin 5 → ZMod 2) ≠ 0 := fun hw h => hw (by
      apply Multiplicative.toAdd.injective
      exact Subtype.ext h)
    have heq : β ⟨q * u * q⁻¹, hquU⟩ = β ⟨u, hu⟩ := by
      by_contra hne'
      have hne'' : ((Multiplicative.toAdd (β ⟨q * u * q⁻¹, hquU⟩) : evenWeight 5) :
          Fin 5 → ZMod 2) ≠ ((Multiplicative.toAdd (β ⟨u, hu⟩) : evenWeight 5) :
          Fin 5 → ZMod 2) := fun h => hne' (Multiplicative.toAdd.injective (Subtype.ext h))
      have h0f : (0 : Fin 5 → ZMod 2) ∈ fixSet₂ a b := mem_fixSet₂.mpr ⟨by decide, rfl, rfl⟩
      have hsub : ({0, ((Multiplicative.toAdd (β ⟨u, hu⟩) : evenWeight 5) : Fin 5 → ZMod 2),
          ((Multiplicative.toAdd (β ⟨q * u * q⁻¹, hquU⟩) : evenWeight 5) : Fin 5 → ZMod 2)} :
          Finset (Fin 5 → ZMod 2)) ⊆ fixSet₂ a b := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · exact h0f
        · exact hx
        · exact hy
      have h3 := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hne'')] at h3
      · omega
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨(hval h0).symm, (hval h0').symm⟩
    have hv : q * u * q⁻¹ * u⁻¹ ∈ blockU K := (blockU K).mul_mem hquU ((blockU K).inv_mem hu)
    have hvZ : q * u * q⁻¹ * u⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
      apply hZ _ hv
      have e : (⟨q * u * q⁻¹ * u⁻¹, hv⟩ : ↥(blockU K)) = ⟨q * u * q⁻¹, hquU⟩ * ⟨u, hu⟩⁻¹ := rfl
      rw [e, map_mul, map_inv, heq, mul_inv_cancel]
    have hsq : (q * u * q⁻¹ * u⁻¹) * (q * u * q⁻¹ * u⁻¹) = 1 := by
      rw [← pow_two]
      exact hKs.2.2.1.2 _ hv
    have hcq := Subgroup.mem_centralizer_iff.mp hvZ q hqK
    have h1 := eq_one_of_conj_fixed hq3 (by rw [hcq, mul_inv_cancel_right]) hsq
    calc q * u * q⁻¹ = (q * u * q⁻¹ * u⁻¹) * u := by group
      _ = u := by rw [h1, one_mul]

theorem mem_centralizer_of_block (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) {K : Subgroup G} (hKc : K ∈ cComp H) (hKs : IsShort2 K)
    (hKa : IsAltType K 5) {q : G} (hqK : q ∈ K) (hq3 : orderOf q = 3)
    (hqN : q ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) :
    q ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq3' : q ^ 3 = 1 := by rw [← hq3]; exact pow_orderOf_eq_one q
  obtain ⟨hel, hVO, -⟩ := vz_facts h331 hyp hH
  set V := VZ T H with hVdef
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := le_normalizer_conjClosure _ H
  have hKH := le_of_mem_cComp hKc
  have hT : IsSylowTwoOf T H := (SecB.minParabolic_of_isHStar h331 hyp hH).isSylow
  have hSK : IsSylowTwoOf (T ⊓ K) K :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hKc) hT
  have hP4 : ∀ α : ↥K →* alternatingGroup (Fin 5), Function.Surjective α →
      α.ker = CFSG.pCore 2 ↥K → Nat.card ↥(((T ⊓ K).subgroupOf K).map α) = 4 :=
    fun α hαs _ => card_of_isSylowTwoOf (SecB.isSylowTwoOf_map_of_surjective hSK α hαs)
  have hVK : V ≤ Subgroup.normalizer (K : Set G) :=
    hVO.trans (P134.pCoreOf_le_normalizer_of_mem_cComp hKc)
  have hcV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsV : ∀ x ∈ V, x * x = 1 := fun x hx => by rw [← pow_two]; exact hel.2 x hx
  have hqV : ∀ x ∈ V, q * x * q⁻¹ ∈ V := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hHN (hKH hqK)) x).mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzV : z ∈ V := le_conjClosure _ _ hz
  have hzT := Subgroup.mem_centralizer_iff.mp (omegaOneCenter_le_centralizer T hz)
  set v := q * z * q⁻¹ with hv
  have hvV : v ∈ V := hqV z hzV
  have hv2V : q * v * q⁻¹ ∈ V := hqV v hvV
  set w := q * v * q⁻¹ * v⁻¹ with hw
  have hwV : w ∈ V := V.mul_mem hv2V (V.inv_mem hvV)
  have hwK : w ∈ K := by
    have h1 : v * q⁻¹ * v⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hVK hvV) _).mp (K.inv_mem hqK)
    have e : w = q * (v * q⁻¹ * v⁻¹) := by rw [hw]; group
    rw [e]
    exact K.mul_mem hqK h1
  have hwQ : w ∈ blockQ K := inf_le_blockQ hel (hKH.trans hHN) ⟨hwK, hwV⟩
  have hu : q * z * q⁻¹ * z⁻¹ = q * w * q⁻¹ * w⁻¹ :=
    conj_mul_inv_eq hq3' (hcV _ hzV _ hvV) (hcV _ hvV _ hv2V) (hsV _ hzV) (hsV _ hv2V)
  have huU : q * z * q⁻¹ * z⁻¹ ∈ blockU K := by
    rw [hu, blockU, Subgroup.commutator_comm]
    have := Subgroup.commutator_mem_commutator hqK hwQ
    rwa [commutatorElement_def] at this
  have huS : ∀ s ∈ T ⊓ K, s * (q * z * q⁻¹ * z⁻¹) = (q * z * q⁻¹ * z⁻¹) * s := by
    intro s hs
    have h1 : q⁻¹ * s * q ∈ T ⊓ K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hqN) s).mp hs
      simpa using this
    have h2 := hzT _ h1.1
    have h3 := hzT _ hs.1
    calc s * (q * z * q⁻¹ * z⁻¹) = q * ((q⁻¹ * s * q) * z) * q⁻¹ * z⁻¹ := by group
      _ = q * (z * (q⁻¹ * s * q)) * q⁻¹ * z⁻¹ := by rw [h2]
      _ = q * z * q⁻¹ * (s * z⁻¹) := by group
      _ = q * z * q⁻¹ * (z⁻¹ * s) := by
        rw [show s * z⁻¹ = z⁻¹ * s by
          calc s * z⁻¹ = z⁻¹ * (z * s) * z⁻¹ := by group
            _ = z⁻¹ * (s * z) * z⁻¹ := by rw [h3]
            _ = z⁻¹ * s := by group]
      _ = (q * z * q⁻¹ * z⁻¹) * s := by group
  have hfix := conj_eq_of_mem_blockU hKs hKa hP4 hqK hq3' hqN huU huS
  have h1 := eq_one_of_conj_fixed hq3' hfix (hsV _ (V.mul_mem hvV (V.inv_mem hzV)))
  calc z * q = (q * z * q⁻¹ * z⁻¹)⁻¹ * (q * z) := by group
    _ = q * z := by rw [h1, inv_one, one_mul]

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
