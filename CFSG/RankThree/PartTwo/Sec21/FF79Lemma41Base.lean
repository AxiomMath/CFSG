module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab


public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.L41

open CFSG CFSG.RankThree.PartTwo.Sec21
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem isSylowOf_card_p {H P : Subgroup G} (h : IsSylowOf p P H) :
    Nat.card P = p ^ (Nat.card H).factorization p := by
  have hp : p.Prime := Fact.out
  obtain ⟨hle, hP, hcop⟩ := h
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  have h1 := Subgroup.relIndex_mul_card P H
  rw [inf_of_le_left hle, ha] at h1
  have hne : P.relIndex H ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  have hf : (P.relIndex H).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop)
  rw [← h1, Nat.factorization_mul hne (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply, hf,
    Nat.Prime.factorization_pow hp, Finsupp.single_eq_same, zero_add, ha]

theorem isSylowOf_of_card_p {H P : Subgroup G} (hle : P ≤ H)
    (hc : Nat.card P = p ^ (Nat.card H).factorization p) : IsSylowOf p P H := by
  have hp : p.Prime := Fact.out
  refine ⟨hle, IsPGroup.of_card hc, ?_⟩
  have h1 := Subgroup.relIndex_mul_card P H
  rw [inf_of_le_left hle, hc] at h1
  have hne : P.relIndex H ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have hpos : 0 < (P.relIndex H).factorization p :=
    Nat.Prime.factorization_pos_of_dvd hp hne hdvd
  have h2 : (P.relIndex H * p ^ (Nat.card H).factorization p).factorization p =
      (Nat.card H).factorization p := by rw [h1]
  rw [Nat.factorization_mul hne (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
    Nat.Prime.factorization_pow hp, Finsupp.single_eq_same] at h2
  omega

theorem exists_sylowOf_p (H : Subgroup G) : ∃ P : Subgroup G, IsSylowOf p P H := by
  have hp : p.Prime := Fact.out
  obtain ⟨P⟩ : Nonempty (Sylow p H) := inferInstance
  refine ⟨(P : Subgroup H).map H.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · exact P.isPGroup'.map H.subtype
  · rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (P.not_dvd_index)

theorem exists_conj_le_sylowOf_p {H P Q : Subgroup G} (hP : IsSylowOf p P H) (hQH : Q ≤ H)
    (hQ : IsPGroup p Q) : ∃ k ∈ H, ∀ x ∈ Q, k * x * k⁻¹ ∈ P := by
  have hp : p.Prime := Fact.out
  obtain ⟨hPH, hPp, hPi⟩ := hP
  let A : Subgroup ↥H := P.subgroupOf H
  let Q' : Subgroup ↥H := Q.subgroupOf H
  have hAp : IsPGroup p A := hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  have hQ'p : IsPGroup p Q' := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  have hAi : ¬ p ∣ A.index := (Nat.Prime.coprime_iff_not_dvd hp).mp hPi
  obtain ⟨S, hS⟩ := hQ'p.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥H (hAp.toSylow hAi) S
  refine ⟨((k : ↥H) : G)⁻¹, H.inv_mem k.2, fun x hx => ?_⟩
  have hxS : (⟨x, hQH hx⟩ : ↥H) ∈ ((k • hAp.toSylow hAi : Sylow p ↥H) : Subgroup ↥H) := by
    rw [hk]
    exact hS (show (⟨x, hQH hx⟩ : ↥H) ∈ Q' from hx)
  rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe,
    Subgroup.mem_smul_pointwise_iff_exists] at hxS
  obtain ⟨s, hs, hseq⟩ := hxS
  have h1 := congrArg Subtype.val hseq
  have hsP : (s : G) ∈ P := hs
  have h2 : ((k : ↥H) : G) * (s : G) * ((k : ↥H) : G)⁻¹ = x := by
    simpa [MulAut.smul_def, MulAut.conj_apply] using h1
  have h3 : ((k : ↥H) : G)⁻¹ * x * ((k : ↥H) : G) = s := by
    rw [← h2]; group
  have : ((k : ↥H) : G)⁻¹ * x * ((k : ↥H) : G)⁻¹⁻¹ = s := by rw [inv_inv]; exact h3
  rw [this]
  exact hsP

theorem card_conjBy (g : G) (H : Subgroup G) : Nat.card ↥(conjBy g H) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem isSylowOf_conjBy {H P : Subgroup G} (h : IsSylowOf p P H) (g : G) :
    IsSylowOf p (conjBy g P) (conjBy g H) := by
  refine isSylowOf_of_card_p (Subgroup.map_mono h.1) ?_
  rw [card_conjBy, card_conjBy]
  exact isSylowOf_card_p h

theorem conjBy_conjBy (g h : G) (H : Subgroup G) :
    conjBy g (conjBy h H) = conjBy (g * h) H := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by group⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨h * y * h⁻¹, ⟨y, hy, rfl⟩, by group⟩

theorem exists_conjBy_eq_sylowOf {H P Q : Subgroup G} (hP : IsSylowOf p P H)
    (hQ : IsSylowOf p Q H) : ∃ k ∈ H, conjBy k Q = P := by
  obtain ⟨k, hk, hkQ⟩ := exists_conj_le_sylowOf_p hP hQ.1 hQ.2.1
  refine ⟨k, hk, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) ?_
  · obtain ⟨y, hy, rfl⟩ := hx
    exact hkQ y hy
  · rw [card_conjBy, isSylowOf_card_p hP, isSylowOf_card_p hQ]

theorem mem_nor_of_forall {V : Subgroup G} {m : G} (h : ∀ y ∈ V, m * y * m⁻¹ ∈ V) :
    m ∈ Nor V := by
  have hle : conjBy m V ≤ V := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have heq : conjBy m V = V :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjBy])
  refine Subgroup.mem_set_normalizer_iff.mpr (fun y => ⟨h y, fun hy => ?_⟩)
  have : m * y * m⁻¹ ∈ conjBy m V := by rw [heq]; exact hy
  obtain ⟨y', hy', hyy⟩ := this
  have : y' = y := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyy
    have h1 : y' * m⁻¹ = y * m⁻¹ := mul_left_cancel (a := m) (by simpa [mul_assoc] using hyy)
    exact mul_right_cancel h1
  exact this ▸ hy'

theorem Op_le (H : Subgroup G) : Op p H ≤ H := Subgroup.map_subtype_le _

theorem Op_conj_mem {H : Subgroup G} {g z : G} (hg : g ∈ H) (hz : z ∈ Op p H) :
    g * z * g⁻¹ ∈ Op p H := by
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * z' * ⟨g, hg⟩⁻¹, ?_, by simp⟩
  exact (CFSG.pCore_normal (p := p) (G := H)).conj_mem z' hz' ⟨g, hg⟩

theorem Op_isPGroup (H : Subgroup G) : IsPGroup p (Op p H) :=
  (CFSG.pCore_isPGroup (p := p) (G := H)).map H.subtype

theorem le_Op_of_normalized {N H : Subgroup G} (hNH : N ≤ H)
    (hn : ∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N) (hc : IsPGroup p N) : N ≤ Op p H := by
  have hN : (N.subgroupOf H).Normal := ⟨fun x hx h => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hn h h.2 x hx⟩
  have hp : IsPGroup p (N.subgroupOf H) := hc.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hle : N.subgroupOf H ≤ pCore p H := le_sSup ⟨hN, hp⟩
  intro x hx
  exact ⟨⟨x, hNH hx⟩, hle hx, rfl⟩

theorem mem_Op_of_centralizes {H : Subgroup G} (hH : IsCharacteristicP p ↥H) {g : G} (hg : g ∈ H)
    (hc : ∀ z ∈ Op p H, g * z = z * g) : g ∈ Op p H := by
  have hmem : (⟨g, hg⟩ : ↥H) ∈ Subgroup.centralizer (pCore p ↥H : Set ↥H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := hc w ⟨w, hw, rfl⟩
    exact Subtype.ext this.symm
  exact ⟨⟨g, hg⟩, hH hmem, rfl⟩

theorem comm_aux {a c j k : G} (haj : Commute a j) (hak : Commute a k) (hac : Commute a c)
    (hcj : Commute c j) (hck : Commute c k) :
    (a * j) * (c * k) * (a * j)⁻¹ * (c * k)⁻¹ = j * k * j⁻¹ * k⁻¹ := by
  have hA : a * (j * c * k * j⁻¹) * a⁻¹ = j * c * k * j⁻¹ :=
    (((haj.mul_right hac).mul_right hak).mul_right haj.inv_right).mul_inv_cancel
  have hw : Commute c (j * k * j⁻¹ * k⁻¹) :=
    (((hcj.mul_right hck).mul_right hcj.inv_right).mul_right hck.inv_right)
  have hC : c * (j * k * j⁻¹ * k⁻¹) * c⁻¹ = j * k * j⁻¹ * k⁻¹ := hw.mul_inv_cancel
  calc (a * j) * (c * k) * (a * j)⁻¹ * (c * k)⁻¹
      = a * (j * c * k * j⁻¹) * a⁻¹ * (k⁻¹ * c⁻¹) := by group
    _ = (j * c * k * j⁻¹) * (k⁻¹ * c⁻¹) := by rw [hA]
    _ = (c * j) * k * j⁻¹ * (k⁻¹ * c⁻¹) := by rw [hcj.eq.symm]
    _ = c * (j * k * j⁻¹ * k⁻¹) * c⁻¹ := by group
    _ = j * k * j⁻¹ * k⁻¹ := hC

theorem centralizes_of_comm_central {J : Subgroup G} (hJ : Group.IsPerfect ↥J) {t : G}
    (ht : ∀ j ∈ J, t * j * t⁻¹ * j⁻¹ ∈ J ⊓ CenS J) : ∀ j ∈ J, j * t = t * j := by
  let S : Subgroup ↥J := (Subgroup.centralizer ({t} : Set G)).subgroupOf J
  have hS : (commutator ↥J) ≤ S := by
    rw [commutator_def, Subgroup.commutator_le]
    intro j _ k _
    show ((⁅j, k⁆ : ↥J) : G) ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hj := ht j j.2
    have hk := ht k k.2
    have hcomm : ∀ x ∈ J, ∀ y ∈ CenS J, x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.mp hy x hx
    set a : G := t * j * t⁻¹ * (j : G)⁻¹ with ha
    set c : G := t * k * t⁻¹ * (k : G)⁻¹ with hc
    have e1 : t * (j : G) * t⁻¹ = a * j := by rw [ha]; group
    have e2 : t * (k : G) * t⁻¹ = c * k := by rw [hc]; group
    have e3 : t * ((j : G) * k * (j : G)⁻¹ * (k : G)⁻¹) * t⁻¹ =
        (t * j * t⁻¹) * (t * k * t⁻¹) * (t * j * t⁻¹)⁻¹ * (t * k * t⁻¹)⁻¹ := by group
    have haj : Commute a j := (hcomm j j.2 a hj.2).symm
    have hak : Commute a k := (hcomm k k.2 a hj.2).symm
    have hac : Commute a c := (hcomm c hk.1 a hj.2).symm
    have hcj : Commute c j := (hcomm j j.2 c hk.2).symm
    have hck : Commute c k := (hcomm k k.2 c hk.2).symm
    have e4 : t * ((j : G) * k * (j : G)⁻¹ * (k : G)⁻¹) * t⁻¹ =
        (j : G) * k * (j : G)⁻¹ * (k : G)⁻¹ := by
      rw [e3, e1, e2]
      exact comm_aux haj hak hac hcj hck
    have : ((⁅j, k⁆ : ↥J) : G) = (j : G) * k * (j : G)⁻¹ * (k : G)⁻¹ := by
      simp [commutatorElement_def]
    rw [this]
    have e5 := e4
    rw [mul_inv_eq_iff_eq_mul] at e5
    exact e5.symm
  have htop : (⊤ : Subgroup ↥J) ≤ S := by
    rw [← Group.isPerfect_def.mp hJ]
    exact hS
  intro j hj
  have := htop (Subgroup.mem_top (⟨j, hj⟩ : ↥J))
  have h2 : j ∈ Subgroup.centralizer ({t} : Set G) := this
  exact Subgroup.mem_centralizer_singleton_iff.mp h2

end CFSG.RankThree.PartTwo.Sec21.FF79.L41
