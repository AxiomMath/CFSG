module

public import CFSG.Sporadic.HNOddCore.FourPairComp
public import CFSG.Sporadic.HNOddCore.SixCheck
public import Certificates.Certificate2084
public import Certificates.Certificate2087
public import Certificates.Certificate2091
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

theorem prep_resHom_of_smul {N : ℕ} {G : Type*} [Group G] [MulAction G (Fin N)] {F : Array ℕ}
    {hF : PtList N F} {K : Subgroup G} (hK : Preserves hF K) (x : K) {t : Array ℕ}
    (ht : ∀ k : Fin F.size, ∃ h : t[(k : ℕ)]! < F.size,
      (x : G) • hF.pt k = hF.pt ⟨t[(k : ℕ)]!, h⟩) :
    PRep F.size t (resHom hK x) := by
  intro k
  obtain ⟨h, he⟩ := ht k
  have e := pt_resHom hK x k
  rw [he] at e
  rw [hF.pt_injective e]

abbrev C6 : Subgroup JH := Subgroup.centralizer {aJ}

theorem om0_cert :
    orbitCertOK InvData.f6Arr.size InvData.s6Perms om0L
    (posArr InvData.f6Arr.size om0L) (orbitRecs InvData.s6Perms om0L
      (posArr InvData.f6Arr.size om0L)).1
    (orbitRecs InvData.s6Perms om0L (posArr InvData.f6Arr.size om0L)).2 = true :=
  orbitCert6 (i := 1) (by norm_num)

theorem hL1 :
    PtList InvData.f6Arr.size om0L := ptList_of_pointsOK (orbitCertOK_spec om0_cert).2.1

theorem om0L_size :
    om0L.size = 1100 := o6_size (i := 1) (by norm_num)

@[expose] def om0X : Array ℕ := om0L.map fun j => InvData.f6Arr[j]!

theorem om0X_size' : om0X.size = om0L.size := by rw [om0X, Array.size_map]

theorem om0X_size : om0X.size = 1100 := by rw [om0X_size', om0L_size]

theorem om0X_get {k : ℕ} (hk : k < om0L.size) : om0X[k]! = InvData.f6Arr[om0L[k]!]! := by
  rw [om0X, getElem!_pos _ k (by simpa using hk), Array.getElem_map, getElem!_pos om0L k hk]

theorem hO1 :
    PtList hnsData.n om0X where
  lt k hk := by
    have hk' : k < om0L.size := by rw [← om0X_size']; exact hk
    rw [om0X_get hk']
    exact hF6.lt _ (hL1.lt k hk')
  inj k hk l hl he := by
    have hk' : k < om0L.size := by rw [← om0X_size']; exact hk
    have hl' : l < om0L.size := by rw [← om0X_size']; exact hl
    rw [om0X_get hk', om0X_get hl'] at he
    exact hL1.inj k hk' l hl' (hF6.inj _ (hL1.lt k hk') _ (hL1.lt l hl') he)

theorem hO1_pt (k : Fin om0X.size) :
    hO1.pt k = hF6.pt (hL1.pt ⟨k, by rw [← om0X_size']; exact k.2⟩) := by
  apply Fin.ext
  rw [PtList.pt_val, PtList.pt_val, PtList.pt_val]
  exact om0X_get (by rw [← om0X_size']; exact k.2)

theorem range_hO1 :
    Set.range hO1.pt = MulAction.orbit S6 (b6 1 (by norm_num)) := by
  rw [orbit6_eq]
  ext y
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, (hO1_pt k).symm⟩
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨⟨k, by rw [om0X_size']; exact k.2⟩, hO1_pt _⟩

theorem hC6 :
    Preserves hO1 C6 := by
  intro g hg k
  have hmem : hO1.pt k ∈ Set.range hO1.pt := ⟨k, rfl⟩
  rw [range_hO1] at hmem
  have hg' : g ∈ S6 := by rw [CJ_t6_eq]; exact hg
  have := orbit_invariant_of_le (le_refl S6) (b6 1 (by norm_num)) ⟨g, hg'⟩ _ hmem
  rw [← range_hO1] at this
  obtain ⟨l, hl⟩ := this
  exact ⟨l, hl.symm⟩

@[expose] def phi6 :
    C6 →* Perm (Fin 1100) :=
  (Equiv.permCongrHom (finCongr om0X_size)).toMonoidHom.comp (resHom hC6)

@[expose] def g6C
    (s : Fin 12) : C6 := ⟨g6 s, g6_mem s.2⟩

theorem om0Gens_get
    {s : ℕ} (hs : s < 12) {k : ℕ} (hk : k < 1100) :
    (om0Gens[s]!)[k]! = (posArr InvData.f6Arr.size om0L)[(InvData.s6Perms[s]!)[om0L[k]!]!]! := by
  have hs' : s < InvData.s6Perms.size := by rw [row6_parts.2.2.2.2.1]; exact hs
  have hk' : k < om0L.size := by rw [om0L_size]; exact hk
  rw [om0Gens, getElem!_pos _ s (by simpa using hs'), Array.getElem_map,
    ← getElem!_pos InvData.s6Perms s hs', restrictTab, getElem!_pos _ k (by simpa using hk'),
    Array.getElem_map, ← getElem!_pos om0L k hk', data_parts.2.2.1]

theorem prep_phi6
    (s : Fin 12) : PRep 1100 om0Gens[(s : ℕ)]! (phi6 (g6C s)) := by
  obtain ⟨s, hs⟩ := s
  have hs' : s < InvData.s6Perms.size := by rw [row6_parts.2.2.2.2.1]; exact hs
  obtain ⟨-, -, -, hcl⟩ := orbitCertOK_spec om0_cert
  refine prep_cast om0X_size (prep_resHom_of_smul hC6 _ fun k => ?_)
  have hk : (k : ℕ) < om0L.size := by rw [← om0X_size']; exact k.2
  obtain ⟨hlt, heq⟩ := hcl k hk s hs'
  have hk1100 : (k : ℕ) < 1100 := by rw [← om0L_size]; exact hk
  rw [om0Gens_get hs hk1100]
  refine ⟨hlt.trans_eq om0X_size'.symm, ?_⟩
  rw [hO1_pt, hO1_pt]
  show g6 s • hF6.pt (hL1.pt _) = _
  obtain ⟨h1, h2⟩ := hact6 s hs' (hL1.pt ⟨k, hk⟩)
  rw [h2]
  congr 1
  apply Fin.ext
  show (InvData.s6Perms[s]!)[om0L[(k : ℕ)]!]! =
    om0L[(posArr InvData.f6Arr.size om0L)[(InvData.s6Perms[s]!)[om0L[(k : ℕ)]!]!]!]!
  exact heq.symm

theorem closure_g6C :
    Subgroup.closure (Set.range g6C) = ⊤ := by
  have h := closure_preimage_eq_top (C := C6) (fun s : Fin 12 => g6_mem s.2) (by
    show Subgroup.centralizer {aJ} = _
    rw [← CJ_t6_eq]
    show Subgroup.closure _ = Subgroup.closure _
    congr 1
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨⟨s, by rw [← row6_parts.2.2.2.2.1]; exact s.2⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨⟨s, by rw [row6_parts.2.2.2.2.1]; exact s.2⟩, rfl⟩)
  exact h

theorem phi6_range :
    phi6.range = arrGen 1100 om0Gens := by
  rw [range_eq_closure phi6 closure_g6C]
  have hsz : om0Gens.size = 12 := by simp [om0Gens, row6_parts.2.2.2.2.1]
  have hO : ∀ k < om0Gens.size, PRep 1100 om0Gens[k]!
      (if h : k < 12 then phi6 (g6C ⟨k, h⟩) else 1) := by
    intro k hk
    have hk' : k < 12 := by rw [← hsz]; exact hk
    rw [dite_eq_left hk']
    exact prep_phi6 ⟨k, hk'⟩
  rw [arrGen_eq hO]
  congr 1
  ext σ
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨⟨s, by rw [hsz]; exact s.2⟩, by dsimp only; rw [dite_eq_left s.2]⟩
  · rintro ⟨⟨k, hk⟩, rfl⟩
    have hk' : k < 12 := by rw [← hsz]; exact hk
    exact ⟨⟨k, hk'⟩, by simp only [dite_eq_left hk']⟩

@[expose] def t6C : C6 := ⟨aJ, mem_centralizer_of_comm rfl⟩

theorem t6C_mem_ker :
    t6C ∈ phi6.ker := by
  rw [MonoidHom.mem_ker]
  apply Equiv.ext
  intro k
  apply (finCongr om0X_size).symm.injective
  apply hO1.pt_injective
  have e := pt_resHom hC6 t6C ((finCongr om0X_size).symm k)
  have e2 : ((finCongr om0X_size).symm (phi6 t6C k)) =
      resHom hC6 t6C ((finCongr om0X_size).symm k) := by
    apply Fin.ext
    simp [phi6, Equiv.permCongrHom, Equiv.permCongr_apply]
  rw [e2, e]
  show aJ • hO1.pt _ = hO1.pt _
  have hfix : hO1.pt ((finCongr om0X_size).symm k) ∈ Set.range hO1.pt := ⟨_, rfl⟩
  rw [range_hO1] at hfix
  have := orbit6_subset_fix (i := 1) (by norm_num) hfix
  rw [Set.mem_ofPred_eq, jR_smul] at this
  exact this

theorem sq_eq_one_of_permJ
    {g : JH} (h : permJ g ^ 2 = 1) : g ^ 2 = 1 :=
  permJ_injective (by rw [map_pow, h, map_one])

theorem orderOf_mk_two {G : Type*} [Group G] {H : Subgroup G} {g : G} (hg : g ∈ H)
    (h2 : g ^ 2 = 1) (h1 : g ≠ 1) : orderOf (⟨g, hg⟩ : H) = 2 := by
  rw [Subgroup.orderOf_mk]
  exact orderOf_eq_prime h2 h1

theorem aJ_sq :
    aJ ^ 2 = 1 := sq_eq_one_of_permJ (by rw [permJ_aJ]; exact order_parts.1)

theorem aJ_ne_one :
    aJ ≠ 1 := by
  intro h
  have e : (⟨aJ, aJ_mem_HJ⟩ : HJ) = 1 := Subtype.ext h
  have := thetaJ_aJ
  rw [e, map_one, Subgroup.coe_one] at this
  exact absurd this.symm (by unfold sig6; decide)

theorem t6C_ne_one :
    t6C ≠ 1 := by
  intro h
  have h' := congrArg Subtype.val h
  rw [Subgroup.coe_one] at h'
  exact aJ_ne_one h'

theorem card_phi6_range_le :
    Nat.card phi6.range ≤ 88704000 := by
  have h := phi6.ker.card_mul_index
  rw [Subgroup.index_ker, card_CJ_t6] at h
  have h2 : 2 ≤ Nat.card phi6.ker := by
    have h1 : (Subgroup.zpowers t6C) ≤ phi6.ker := by
      rw [Subgroup.zpowers_le]
      exact t6C_mem_ker
    have hz : Nat.card (Subgroup.zpowers t6C) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_mk_two _ aJ_sq aJ_ne_one
    rw [← hz]
    exact Subgroup.card_le_of_le h1
  have : 2 * Nat.card phi6.range ≤ 177408000 := by
    rw [← h]
    exact Nat.mul_le_mul_right _ h2
  omega

end CFSG.Sporadic.HNOddCore
