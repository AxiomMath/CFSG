module

public import CFSG.Quasithin.Background.HFCode24
public import Certificates.Certificate490031

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

theorem h165All :
    forallGreedyAll pos24s2 inv24s2 predH165 6 [] = true :=
  Certificates.certificate490031

theorem h165Greedy {k : ℕ}
    (hk : k ≤ 6) : forallGreedy T24s2.invols predH165 k [] = true :=
  (forallGreedyP_eq pos24s2_eq predH165 k []).symm.trans (forallGreedyAll_le 6 [] h165All k hk)

theorem predH165_spec {l : List T24s2.Elem} (hl : IndepList l)
    (h : predH165 l = true) (hlen : l.length = 6)
    (hd : 11 - Nat.log 2 (fixMasks 11 codeAct24 l).length ≤ 7) :
    ∀ x ∈ subprods l, T24s2.arr x ∈ ksRefArrs := by
  have hinv : ∀ a ∈ l, a * a = 1 := (isCommInvol_of_indepList hl).1
  rw [predH165, Bool.and_eq_true, codeFixMasks24_eq hinv] at h
  obtain ⟨-, h⟩ := h
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem] at h
  rcases h with (h | h) | h
  · exact absurd hlen h
  · omega
  · exact h

theorem ksRefArrs_length : ksRefArrs.length = 64 := by
  decide +kernel

theorem ksRefArrs_nodup : ksRefArrs.Nodup := by
  decide +kernel

theorem arr_injective_T24s2 :
    Function.Injective (fun p : T24s2.Elem => T24s2.arr p) := by
  intro p q h
  apply T24s2.perm_injective
  ext i
  rw [T24s2.perm_val, T24s2.perm_val]
  exact congrArg (fun a => a[(i : ℕ)]!) h

theorem subprods_eq_of_ref {l l' : List T24s2.Elem}
    (hl : IndepList l) (hl' : IndepList l') (hlen : l.length = 6) (hlen' : l'.length = 6)
    (h : ∀ x ∈ subprods l, T24s2.arr x ∈ ksRefArrs)
    (h' : ∀ x ∈ subprods l', T24s2.arr x ∈ ksRefArrs) :
    ∀ s, s ∈ subprods l ↔ s ∈ subprods l' := by
  have hinj : Function.Injective (fun p : T24s2.Elem => T24s2.arr p) := arr_injective_T24s2
  have hmapl : ((subprods l).map (fun p : T24s2.Elem => T24s2.arr p)).Nodup :=
    (nodup_subprods hl).map hinj
  have hmapl' : ((subprods l').map (fun p : T24s2.Elem => T24s2.arr p)).Nodup :=
    (nodup_subprods hl').map hinj
  have hlenl : (subprods l).length = 64 := by rw [length_subprods, hlen]; norm_num
  have hlenl' : (subprods l').length = 64 := by rw [length_subprods, hlen']; norm_num
  have hcardl : (((subprods l).map (fun p : T24s2.Elem => T24s2.arr p)).toFinset).card = 64 := by
    rw [List.toFinset_card_of_nodup hmapl, List.length_map, hlenl]
  have hcardl' : (((subprods l').map (fun p : T24s2.Elem => T24s2.arr p)).toFinset).card = 64 := by
    rw [List.toFinset_card_of_nodup hmapl', List.length_map, hlenl']
  have hcardks : ksRefArrs.toFinset.card = 64 := by
    rw [List.toFinset_card_of_nodup ksRefArrs_nodup, ksRefArrs_length]
  have heql : ((subprods l).map (fun p : T24s2.Elem => T24s2.arr p)).toFinset =
      ksRefArrs.toFinset :=
    Finset.eq_of_subset_of_card_le
      (fun a ha => by
        rw [List.mem_toFinset] at ha
        obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ha
        exact List.mem_toFinset.2 (h s hs))
      (by rw [hcardks, hcardl])
  have heql' : ((subprods l').map (fun p : T24s2.Elem => T24s2.arr p)).toFinset =
      ksRefArrs.toFinset :=
    Finset.eq_of_subset_of_card_le
      (fun a ha => by
        rw [List.mem_toFinset] at ha
        obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ha
        exact List.mem_toFinset.2 (h' s hs))
      (by rw [hcardks, hcardl'])
  have himage : ∀ s : T24s2.Elem,
      (s ∈ subprods l ↔ T24s2.arr s ∈
        ((subprods l).map (fun p : T24s2.Elem => T24s2.arr p)).toFinset) := by
    intro s
    rw [List.mem_toFinset]
    refine ⟨fun hs => List.mem_map.2 ⟨s, hs, rfl⟩, fun hm => ?_⟩
    obtain ⟨s', hs', harr⟩ := List.mem_map.1 hm
    have hss' : s' = s := hinj harr
    simpa [hss'] using hs'
  have himage' : ∀ s : T24s2.Elem,
      (s ∈ subprods l' ↔ T24s2.arr s ∈
        ((subprods l').map (fun p : T24s2.Elem => T24s2.arr p)).toFinset) := by
    intro s
    rw [List.mem_toFinset]
    refine ⟨fun hs => List.mem_map.2 ⟨s, hs, rfl⟩, fun hm => ?_⟩
    obtain ⟨s', hs', harr⟩ := List.mem_map.1 hm
    have hss' : s' = s := hinj harr
    simpa [hss'] using hs'
  intro s
  rw [himage s, himage' s, heql, heql']

variable {V : Type*} [CommGroup V] {L M : Subgroup (MulAut V)}

theorem chainH165
    (hLM : IsOver L M) {e : V ≃* W11}
    (he : L.map (congrHom e) = (rhoC11 AutPerm le_rfl).range) {A : Subgroup (MulAut V)}
    (hA : A ≤ M) (hAe : IsElemAbelian2 A) {k : ℕ} (hk : k ≤ 6) (hcard : Nat.card A = 2 ^ k) :
    ∃ g : ↥AutPerm, ∃ l : List T24s2.Elem, IndepList l ∧ predH165 l = true ∧
      IsChainSub (chainAut e psiC24 phi24 g) l A ∧ l.length = k := by
  obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel psiC24 (rhoC11_injective _ _) phi24
    (T24s2.toSub_injective _ _) card_T24s2 (fun _ h1 h2 => T24s2.mem_invols h1 h2)
    (h165Greedy hk) e (map_le_rangeC24 hLM he hA) hAe hcard
  have hcl := card_of_chainSub hchain (chainAutC24_injective e g) hind
  rw [hcard] at hcl
  exact ⟨g, l, hind, hpred, hchain, (Nat.pow_right_injective (le_refl 2) hcl).symm⟩

private theorem congrHom_apply24 {V W : Type*} [CommGroup V] [CommGroup W] (e : V ≃* W)
    (x : MulAut V) (w : W) : congrHom e x w = e (x (e.symm w)) := rfl

private theorem chainAut_apply24 {V : Type*} [CommGroup V] {n : ℕ} {K P : Type*} [Group K]
    [Finite K] [Group P] (e : V ≃* Wn n) (ψ : K →* MulAut (Wn n)) (φ : P →* K) (g : K)
    (s : P) (v : V) :
    chainAut e ψ φ g s v = (twistEquiv e ψ g).symm (ψ (φ s) (twistEquiv e ψ g v)) := rfl

theorem chain_conj_of_subprods_eq {e : V ≃* W11}
    (he : L.map (congrHom e) = (rhoC11 AutPerm le_rfl).range) {g g' : ↥AutPerm}
    {l l' : List T24s2.Elem} {A A' : Subgroup (MulAut V)}
    (hA : IsChainSub (chainAut e psiC24 phi24 g) l A)
    (hA' : IsChainSub (chainAut e psiC24 phi24 g') l' A')
    (hll : ∀ s, s ∈ subprods l ↔ s ∈ subprods l') :
    ∃ c ∈ L, A' = A.map (MulAut.conj c).toMonoidHom := by
  have hyL : psiC24 (g'⁻¹ * g) ∈ L.map (congrHom e) := by
    rw [he]
    exact ⟨g'⁻¹ * g, rfl⟩
  obtain ⟨c, hcL, hc⟩ := Subgroup.mem_map.1 hyL
  have hkeyA : psiC24 (g'⁻¹ * g) = (psiC24 g')⁻¹ * psiC24 g := by
    rw [map_mul, map_inv]
  have hkeyB : ∀ w : W11, (psiC24 (g'⁻¹ * g)) w = e (c (e.symm w)) := by
    intro w
    have h : (congrHom e c) w = (psiC24 (g'⁻¹ * g)) w :=
      congrArg (fun f : MulAut W11 => f w) hc
    rw [congrHom_apply24 e c w] at h
    exact h.symm
  have hkeyC : ∀ w : W11, (psiC24 g')⁻¹ (psiC24 g w) = e (c (e.symm w)) := by
    intro w
    rw [← MulAut.mul_apply, ← hkeyA, hkeyB]
  have hsymm : ∀ (h : ↥AutPerm) (Z : W11),
      (twistEquiv e psiC24 h).symm Z = e.symm ((psiC24 h)⁻¹ Z) := fun _ _ => rfl
  have hconj : ∀ s : T24s2.Elem, chainAut e psiC24 phi24 g' s =
      c * chainAut e psiC24 phi24 g s * c⁻¹ := by
    intro s
    ext v
    rw [chainAut_apply24 e psiC24 phi24 g' s v, MulAut.mul_apply, MulAut.mul_apply,
      chainAut_apply24 e psiC24 phi24 g s (c⁻¹ v)]
    have hv : twistEquiv e psiC24 g' v = twistEquiv e psiC24 g (c⁻¹ v) := by
      show psiC24 g' (e v) = psiC24 g (e (c⁻¹ v))
      have h := hkeyC (e (c⁻¹ v))
      have h' : (psiC24 g')⁻¹ (psiC24 g (e (c⁻¹ v))) = e v := by
        simpa only [MulEquiv.symm_apply_apply, MulAut.apply_inv_self] using h
      have h2 := congrArg (psiC24 g') h'
      rw [MulAut.apply_inv_self] at h2
      exact h2.symm
    rw [hv]
    rw [hsymm g' (psiC24 (phi24 s) (twistEquiv e psiC24 g (c⁻¹ v)))]
    have hC := hkeyC ((psiC24 g)⁻¹ (psiC24 (phi24 s) (twistEquiv e psiC24 g (c⁻¹ v))))
    rw [MulAut.apply_inv_self] at hC
    rw [hC, MulEquiv.symm_apply_apply]
    rfl
  refine ⟨c, hcL, ?_⟩
  ext a
  rw [hA' a, Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨chainAut e psiC24 phi24 g s, (hA _).2 ⟨s, (hll s).2 hs, rfl⟩, ?_⟩
    change MulAut.conj c (chainAut e psiC24 phi24 g s) = chainAut e psiC24 phi24 g' s
    rw [MulAut.conj_apply]
    exact (hconj s).symm
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨s, hs, rfl⟩ := (hA b).1 hb
    refine ⟨s, (hll s).1 hs, ?_⟩
    change MulAut.conj c (chainAut e psiC24 phi24 g s) = chainAut e psiC24 phi24 g' s
    rw [MulAut.conj_apply]
    exact (hconj s).symm

theorem h165_offender_chain
    [Finite V] (hLM : IsOver L M) (h : MathieuCode24 L ⊤ ⊥) {e : V ≃* W11}
    (he : L.map (congrHom e) = (rhoC11 AutPerm le_rfl).range) {A : Subgroup (MulAut V)}
    (hA : IsFOneOffender M A) :
    ∃ (g : ↥AutPerm) (l : List T24s2.Elem), IndepList l ∧ l.length = 6 ∧
      IsChainSub (chainAut e psiC24 phi24 g) l A ∧ ∀ x ∈ subprods l, T24s2.arr x ∈ ksRefArrs := by
  obtain ⟨⟨hAM, hA1, hAe⟩, hoff⟩ := hA
  have : Finite (MulAut V) := finite_mulAut V
  obtain ⟨k, hk⟩ := exists_card_eq_two_pow_of_isElemAbelian (isElemAbelian2_iff.mp hAe)
  have hk6 : k ≤ 6 := code24_card_le hLM h hAM hAe hk
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    rw [hk0', pow_zero] at hk
    exact hA1 (Subgroup.eq_bot_of_card_eq A hk)
  obtain ⟨g, l, hind, hpred, hchain, hlen⟩ := chainH165 hLM he hAM hAe hk6 hk
  have hpredHF : predHF24 l = true := by
    have hh := hpred
    rw [predH165, Bool.and_eq_true] at hh
    exact hh.1
  have hr := rkIdx_fixV_chainC24 hchain
  have hrk : rk ↥A = k := by
    unfold rk
    rw [hk, padicValNat.prime_pow]
  have hle : 11 - Nat.log 2 (fixMasks 11 codeAct24 l).length ≤ l.length + 1 := by
    have hh := hoff
    rw [hr, hrk, ← hlen] at hh
    exact hh
  have h7 : 7 ≤ 11 - Nat.log 2 (fixMasks 11 codeAct24 l).length :=
    (predHF24_spec hind hpredHF).1 (by rw [hlen]; exact hk1) hle
  have hk6' : k = 6 := by
    have hh := hoff
    rw [hr, hrk] at hh
    omega
  have hlen6 : l.length = 6 := by rw [hlen, hk6']
  have hd : 11 - Nat.log 2 (fixMasks 11 codeAct24 l).length ≤ 7 := by
    have hh := hoff
    rw [hr, hrk, hk6'] at hh
    omega
  exact ⟨g, l, hind, hlen6, hchain, predH165_spec hind hpred hlen6 hd⟩

theorem h165_one
    [Finite V] (hLM : IsOver L M) (h : MathieuCode24 L ⊤ ⊥) {A B : Subgroup (MulAut V)}
    (hA : IsFOneOffender M A) (hB : IsFOneOffender M B) :
    ∃ c ∈ L, B = A.map (MulAut.conj c).toMonoidHom := by
  obtain ⟨e, he⟩ := code24_std h
  obtain ⟨g, l, hind, hlen, hchainA, harrA⟩ := h165_offender_chain hLM h he hA
  obtain ⟨g', l', hind', hlen', hchainB, harrB⟩ := h165_offender_chain hLM h he hB
  exact chain_conj_of_subprods_eq he hchainA hchainB
    (subprods_eq_of_ref hind hind' hlen hlen' harrA harrB)

end CFSG.Quasithin.H.Mathieu
