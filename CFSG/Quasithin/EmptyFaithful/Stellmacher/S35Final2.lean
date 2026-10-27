module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35FnA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.II

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem back_of_PD (hS : Sit H M S) {β α' : Geo H M} (hp : S34.PD β α') :
    ∃ m γ' : Geo H M, Back H M β α' m γ' := by
  obtain ⟨m, γ', hm, hγ, h1, h2, -⟩ := Std.PD_geodesic hS hp
  exact ⟨m, γ', hm, hγ, h1, h2⟩

omit [Finite G] in
theorem noTransvII_of_lem (h81 : Lem81II H M) (h191 : Lem191 H M) : NoTransvII H M := by
  intro β hβ hsec y hy hyQ hidx
  obtain ⟨E, hE1, hE2, hE3, hE4, hE5, -, -⟩ := h81 β hβ hsec y hy hyQ hidx
  exact h191 β hβ E hE1 hE2 hE3 hE4 hE5

theorem lemma7s_of_steps (hS : Sit H M S) (h3 : Claim3 H M) (hTT : ClaimTT H M)
    (hs1 : Step1 H M) (hs2 : Step2L H M) (hs3 : Step3 H M) : Lemma7s H M := by
  intro β α' hp ht hZ x hx hxQ K hVK hKW hKi hKx hW
  obtain ⟨m, γ', hB⟩ := back_of_PD hS hp
  have hT := hTT β α' m γ' hp hB ht
  have hcen : ∀ w ∈ Wb β, ∀ z ∈ Zv α', ⁅w, z⁆ = 1 := by
    intro w hw z hz
    have h1 : ⁅z, w⁆ ∈ ⁅Vn β, Wb β⁆ := Subgroup.commutator_mem_commutator (hZ hz) hw
    rw [Std.comm_Vn_Wb hS β] at h1
    rw [← commutatorElement_inv, Subgroup.mem_bot.mp h1]
    simp
  have hWm : ¬ Wb β ≤ stab m := fun h => hW fun w hw => h3 β α' m γ' hp hB ⟨hw, h hw⟩
  have hN := hs1 β α' m γ' hp hB ht hT hcen hWm
  have hxs : x ∈ stab β := (Std.PD_Vn_le_stab hS hp).2 hx
  have hx2 : x ^ 2 ∈ Qv β := by
    rw [(Std.Vn_isElemAbelian hS α').2 x hx]
    exact (Qv β).one_mem
  obtain ⟨K', hK', hKK⟩ := hs2 hN β hp.vδ x hxs hxQ hx2 K hVK hKW hKi hKx
  exact hs3 hN β hp.vδ x hxs hxQ K' hK' fun h hh => hKx h (hKK hh)

theorem claim10Ne_of_nodes (hS : Sit H M S) (hcrit : PDCrit H M) (hLP : ClaimLP H M)
    (hTT : ClaimTT H M) (hA : Claim10A H M) (hB : Claim10B H M) (hC : Claim10C H M) :
    ∃ δ δ' : Geo H M, Lam δ δ' := by
  by_contra hne'
  have hne : ∀ δ δ' : Geo H M, ¬ Lam δ δ' := fun δ δ' h => hne' ⟨δ, δ', h⟩
  obtain ⟨β, α', hp, ht⟩ := hLP
  obtain ⟨m, γ', hb⟩ := back_of_PD hS hp
  have hT := hTT β α' m γ' hp hb ht
  obtain ⟨α, hα, hc⟩ := hcrit β α' hp
  by_cases h1 : Wl α ≤ Qv γ'
  · by_cases h2 : Vn α' ≤ Qv β
    · exact hB hne α β α' m γ' hc hα hb ht hT h1 h2
    · exact hC hne α β α' m γ' hc hα hb ht hT h1 h2
  · exact hA hne α β α' m γ' hc hα hb ht hT h1

theorem partC_false (hS : Sit H M S) (hb7 : 7 ≤ bMin H M) (hSym : Claim10Sym H M)
    (h16 : Claim16a H M) (hTT : ClaimTT H M) (h3 : Claim3 H M) (h3a : Claim3a H M)
    (hZinf : ZvInf H M) (h192 : Lem192 H M) (h8C : Claim8aC H M) (hs1 : Step1 H M)
    (hs2C : Step2C H M) (hs3 : Step3 H M) {β α' : Geo H M} (hL : Lam β α') : False := by
  have hL' : Lam α' β := hSym β α' hL
  obtain ⟨m, γ', hB⟩ := back_of_PD hS hL.1
  obtain ⟨hZW, hidx, -⟩ := h192 β α' m γ' hL hB
  have hHT := h16 β α' hL
  have hT := hTT β α' m γ' hL.1 hB hHT
  have hab := Std.Wb_comm_of_b7 hS hb7 β
  have hcen : ∀ w ∈ Wb β, ∀ z ∈ Zv α', ⁅w, z⁆ = 1 := by
    intro w hw z hz
    show w * z * w⁻¹ * z⁻¹ = 1
    rw [hab w hw z (hZW hz)]
    group
  have hWm : ¬ Wb β ≤ stab m := fun h => by
    have : Wb β ≤ stab α' := fun w hw => h3 β α' m γ' hL.1 hB ⟨hw, h hw⟩
    have h1 := Subgroup.relIndex_eq_one.mpr (le_inf le_rfl this : Wb β ≤ Wb β ⊓ stab α')
    omega
  have hN := hs1 β α' m γ' hL.1 hB hHT hT hcen hWm
  have hne : (Delta0 β α').Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hall : ∀ l ∈ nbrs β, Vn α' ≤ Subgroup.normalizer (Zv l : Set G) := fun l hl => by
      by_contra h
      exact (Set.eq_empty_iff_forall_notMem.mp hne) l ⟨hl, h⟩
    have hQ : Vn α' ≤ Qv β := fun x hx =>
      hZinf β hL.1.vδ x ((Std.PD_Vn_le_stab hS hL.1).2 hx) fun l hl => hall l hl hx
    have hc : ⁅Vn β, Vn α'⁆ ≤ Zv β ⊓ Vn α' :=
      le_inf ((Subgroup.commutator_mono le_rfl hQ).trans (Std.comm_Vn_Qv hS hL.1.vδ).le)
        ((Std.PD_comm_le hS hL.1).trans inf_le_right)
    have hz : Zv β ⊓ Vn α' = ⊥ := Fn.inf_eq_bot_of_card_two (hS.cardZ5 β hL.1.vδ) hL.2
    exact (h3a β α' m γ' hL.1 hB).1 (le_bot_iff.mp (hz ▸ hc))
  obtain ⟨l, hl⟩ := hne
  obtain ⟨x, hxV, hxM, hxt, hxW⟩ := h8C β α' m γ' hL hB l hl
  have hxs : x ∈ stab β := (Std.PD_Vn_le_stab hS hL.1).2 hxV
  have hxQ : x ∉ Qv β := fun hq =>
    hxM (stab_le_normalizer_Zv hS.glob.amalg l (Std.Qv_le_stab hS hl.1 hq))
  obtain ⟨K, hK, hKx⟩ := hs2C hN β hL.1.vδ hab (Zv α') (hS.cardZ5 α' hL.1.vδ') hZW hL'.2 l
    hl.1 x hxs hxM hxt hxW
  exact hs3 hN β hL.1.vδ x hxs hxQ K hK hKx

omit [Finite G] in
theorem back_reverse (hb5 : bMin H M = 5) {β α' la γ lb : Geo H M} (hp : S34.PD β α')
    (hla : la ∈ nbrs β) (hγla : γ ∈ nbrs la) (hB : Back H M β α' lb γ) :
    Back H M α' β la γ := by
  obtain ⟨hlb, hγlb, h1, h2⟩ := hB
  have hd := hp.dist_eq
  have e1 : dist α' lb = 1 := dist_eq_one_iff_adj.mpr hlb
  have e2 : dist lb γ = 1 := dist_eq_one_iff_adj.mpr hγlb
  have e3 : dist la γ = 1 := dist_eq_one_iff_adj.mpr hγla
  have e4 : dist β la = 1 := dist_eq_one_iff_adj.mpr hla
  have e3' : dist γ la = 1 := by rw [CosetGeom.dist_comm]; exact e3
  have e4' : dist la β = 1 := by rw [CosetGeom.dist_comm]; exact e4
  have t1 : dist α' γ ≤ dist α' lb + dist lb γ := CosetGeom.dist_triangle rfl α' lb γ
  have t2 : dist α' la ≤ dist α' γ + dist γ la := CosetGeom.dist_triangle rfl α' γ la
  have t3 : dist α' β ≤ dist α' la + dist la β := CosetGeom.dist_triangle rfl α' la β
  have e5 : dist α' β = dist β α' := CosetGeom.dist_comm _ _
  refine ⟨hla, hγla, ?_, ?_⟩ <;> omega

theorem thmB_false (hS : Sit H M S) (hb5 : bMin H M = 5) (hZb : ZvBlock H M)
    (h16 : Claim16a H M) (hTT : ClaimTT H M) (hRC : RCent H M) (hBa : ThmBa H M)
    (hNd : NbarDich H M) (hSub : SuborbitDich H M) (hc23 : ThmBcase23 H M)
    (hc4 : ThmBcase4 H M) (h6b : Claim6b H M) (hSym : Claim10Sym H M) {β α' : Geo H M}
    (hL : Lam β α') : False := by
  have hL' : Lam α' β := hSym β α' hL
  have hp := hL.1
  obtain ⟨lb, γ, hB⟩ := back_of_PD hS hp
  have hd := hp.dist_eq
  obtain ⟨hlb, hγlb, h1, h2⟩ := hB
  have hdγ : dist γ β = 2 := by rw [CosetGeom.dist_comm]; omega
  obtain ⟨la, hla, hγla, hγβ⟩ := Std.dist_eq_two_iff.mp hdγ
  have hB : Back H M β α' lb γ := ⟨hlb, hγlb, h1, h2⟩
  have hB' : Back H M α' β la γ := back_reverse hb5 hp hla hγla hB
  have hT := hTT β α' lb γ hp hB (h16 β α' hL)
  have hT' := hTT α' β la γ hL'.1 hB' (h16 α' β hL')
  obtain ⟨r, hr, hrla, hrlb⟩ := hBa hb5 β la γ lb α' hL hL' hla hγla hB
  have hrV : r ∈ Vn β ⊓ Vn α' := Std.PD_comm_le hS hp hr
  have hcomm : ∀ v ∈ Vn γ, ⁅r, v⁆ = 1 := by
    intro v hv
    have := Std.Vn_commute_dist hS (δ := β) (ρ := γ) (by omega) r hrV.1 v hv
    show r * v * r⁻¹ * v⁻¹ = 1
    rw [this]
    group
  have hrTb : ∀ q ∈ Qv lb ⊓ That2 α' lb, ⁅q, r⁆ ∈ Zv α' := fun q hq =>
    hRC β α' lb γ hp hB hT r hr q hq.2
  have hrTa : ∀ q ∈ Qv la ⊓ That2 β la, ⁅q, r⁆ ∈ Zv β := fun q hq =>
    hRC α' β la γ hL'.1 hB' hT' r (by rw [Subgroup.commutator_comm]; exact hr) q hq.2
  have vla : vtype la = true := Std.vtype_nbr_S5 hp.vδ hla
  have vγ : vtype γ = false := Std.vtype_nbr_S3 vla hγla
  have hla' : la ∈ nbrs γ := Std.mem_nbrs_symm.mp hγla
  have hlb' : lb ∈ nbrs γ := Std.mem_nbrs_symm.mp hγlb
  have hβla : β ∈ nbrs la := Std.mem_nbrs_symm.mp hla
  have hα'lb : α' ∈ nbrs lb := Std.mem_nbrs_symm.mp hlb
  have hα'γ : α' ≠ γ := by
    intro h
    have : dist α' γ = 2 := by
      have := hB'.2.2.2
      have := hB'.2.2.1
      have e : dist α' β = 4 := by rw [CosetGeom.dist_comm]; omega
      omega
    rw [h, CosetGeom.dist_self] at this
    omega
  have hβγ : β ≠ γ := fun h => hγβ h.symm
  by_cases hsb : S34.SameBlock γ la lb
  · have hZ := (hZb γ la lb vγ hla' hlb').mpr hsb
    exact hL.2 ((Std.Zv_le_Zv_of_nbr hS hp.vδ hla).trans
      (hZ.le.trans (Std.Zv_le_Vn hlb)))
  · rcases hNd with hF | hT4
    · exact hc23 h6b γ la lb β α' vγ hla' hlb' hβla hβγ hα'lb hα'γ hsb (Or.inl hF) r hrV hrlb
        hcomm hrTb hrTa
    · rcases hSub γ la lb vγ hla' hlb' hsb with h1 | h10
      · exact hc23 h6b γ la lb β α' vγ hla' hlb' hβla hβγ hα'lb hα'γ hsb (Or.inr h1) r hrV
          hrlb hcomm hrTb hrTa
      · exact hc4 hT4 γ la lb β α' vγ hla' hlb' hβla hβγ hα'lb hα'γ hsb h10 r hrV hrla hrlb
          hcomm hrTb hrTa

theorem caseII_false_of_nodes (hS : Sit H M S)
    (hcrit : PDCrit H M) (hLP : ClaimLP H M) (hTT : ClaimTT H M) (h16 : Claim16a H M)
    (h3 : Claim3 H M) (h3a : Claim3a H M) (hRC : RCent H M) (hZb : ZvBlock H M)
    (hZinf : ZvInf H M) (hA : Claim10A H M) (hB : Claim10B H M) (hC : Claim10C H M)
    (hSym : Claim10Sym H M) (h6b : Claim6b H M) (hs1 : Step1 H M) (hs3 : Step3 H M)
    (h192 : 7 ≤ bMin H M → Lem192 H M) (h8C : 7 ≤ bMin H M → Claim8aC H M)
    (hs2C : 7 ≤ bMin H M → Step2C H M)
    (hBa : ThmBa H M) (hNd : NbarDich H M) (hSub : SuborbitDich H M)
    (hc23 : ThmBcase23 H M) (hc4 : ThmBcase4 H M) : False := by
  obtain ⟨β, α', hL⟩ := claim10Ne_of_nodes hS hcrit hLP hTT hA hB hC
  have h5 := hS.b5
  obtain ⟨k, hk⟩ := hS.glob.odd
  by_cases hb : bMin H M = 5
  · exact thmB_false hS hb hZb h16 hTT hRC hBa hNd hSub hc23 hc4 h6b hSym hL
  · have hb7 : 7 ≤ bMin H M := by omega
    exact partC_false hS hb7 hSym h16 hTT h3 h3a hZinf (h192 hb7) (h8C hb7) hs1 (hs2C hb7) hs3 hL

end S35.II

end F53.Stellmacher

end CFSG.Quasithin
