module

public import CFSG.Quasithin.Background.HA5Weyl
public import CFSG.Quasithin.Background.F1Cartan
public import CFSG.Quasithin.EmptyFaithful.S1422Local
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.H.A5W CFSG.QuasithinUnique.A5.Delta5

namespace FA5

variable {G : Type} [Group G] [Finite G] {L S : Subgroup G}

theorem y5_mem_normalizer_klein :
    (⟨y5, y5_alt⟩ : Alt5) ∈ Subgroup.normalizer (kleinStd : Set Alt5) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have key : ∀ x : Equiv.Perm (Fin 5), x ∈ kleinSet ↔ y5 * x * y5⁻¹ ∈ kleinSet := by
    decide +kernel
  rw [mem_kleinStd, mem_kleinStd]
  exact key h

theorem card_normalizer_kleinStd :
    Nat.card (Subgroup.normalizer (kleinStd : Set Alt5)) = 12 := by
  have h60 : Nat.card Alt5 = 60 := a5_card
  set N := Subgroup.normalizer (kleinStd : Set Alt5) with hN
  have hle : kleinStd ≤ N := Subgroup.le_normalizer
  have h4 : 4 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le hle
    rwa [card_kleinStd] at this
  have hord : orderOf (⟨y5, y5_alt⟩ : Alt5) = 3 := by
    apply orderOf_eq_prime
    · exact Subtype.ext (by simpa using y5_pow_three)
    · intro h
      exact y5_ne_one (by simpa using congrArg Subtype.val h)
  have h3 : 3 ∣ Nat.card N := by
    have h1 : orderOf (⟨⟨y5, y5_alt⟩, y5_mem_normalizer_klein⟩ : N) = 3 := by
      rw [← hord]
      exact Subgroup.orderOf_mk _ _
    rw [← h1]
    exact orderOf_dvd_natCard _
  have h12 : 12 ∣ Nat.card N := by
    have : Nat.Coprime 4 3 := by norm_num
    have h := this.mul_dvd_of_dvd_of_dvd h4 h3
    simpa using h
  have hdvd : Nat.card N ∣ 60 := h60 ▸ Subgroup.card_subgroup_dvd_card N
  have hne : Nat.card N ≠ 60 := by
    intro h
    have htop : N = ⊤ := Subgroup.card_eq_iff_eq_top N |>.mp (by rw [h, h60])
    have hw : (⟨w5, w5_alt⟩ : Alt5) ∈ N := htop ▸ Subgroup.mem_top _
    obtain ⟨x, hx, hxw⟩ := w5_not_norm
    have hxA : x ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      exact kleinSet_alt x hx
    exact hxw ((Subgroup.mem_normalizer_iff.mp hw ⟨x, hxA⟩).mp hx)
  obtain ⟨c, hc⟩ := h12
  have hc' : c ∣ 5 := by
    have : 12 * c ∣ 12 * 5 := by simpa [hc] using hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hc' with h | h
  · simp [hc, h]
  · exfalso
    apply hne
    simp [hc, h]

theorem index_normalizer_kleinStd : (Subgroup.normalizer (kleinStd : Set Alt5)).index = 5 := by
  have h := Subgroup.card_mul_index (Subgroup.normalizer (kleinStd : Set Alt5))
  rw [card_normalizer_kleinStd, a5_card] at h
  omega

theorem card_eq_four_of_sylow {T : Subgroup Alt5} (hT : IsPGroup 2 T) (hodd : ¬ 2 ∣ T.index) :
    Nat.card T = 4 := by
  obtain ⟨a, ha⟩ := hT.exists_card_eq
  have h := Subgroup.card_mul_index T
  rw [a5_card, ha] at h
  have ha2 : a ≤ 2 := by
    by_contra hlt
    have h8 : 2 ^ 3 ∣ 60 := by
      rw [← h]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
    norm_num at h8
  interval_cases a
  · exfalso
    apply hodd
    simp at h
    omega
  · exfalso
    apply hodd
    simp at h
    omega
  · simpa using ha

theorem index_normalizer_sylow_alt5 {T : Subgroup Alt5} (hT : IsPGroup 2 T)
    (hodd : ¬ 2 ∣ T.index) : (Subgroup.normalizer (T : Set Alt5)).index = 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : (Nat.card Alt5).factorization 2 = 2 := by
    rw [a5_card]
    decide +kernel
  let PT : Sylow 2 Alt5 :=
    Sylow.ofCard T (by rw [card_eq_four_of_sylow hT hodd, hf]; norm_num)
  let PV : Sylow 2 Alt5 := Sylow.ofCard kleinStd (by rw [card_kleinStd, hf]; norm_num)
  have h1 := Sylow.card_eq_index_normalizer PT
  have h2 := Sylow.card_eq_index_normalizer PV
  have hT' : (PT : Subgroup Alt5) = T := Sylow.coe_ofCard _ _
  have hV' : (PV : Subgroup Alt5) = kleinStd := Sylow.coe_ofCard _ _
  have h1' : Nat.card (Sylow 2 Alt5) = (Subgroup.normalizer (T : Set Alt5)).index := by
    rw [← hT']
    exact h1
  have h2' : Nat.card (Sylow 2 Alt5) = 5 := by
    have h5 := index_normalizer_kleinStd
    rw [← hV'] at h5
    exact h2.trans h5
  rw [← h1', h2']

theorem index_borelOf_of_alt5 (hsyl : IsSylowTwoOf (S ⊓ L) L) (e : OTwoQuot L ≃* Alt5) :
    ((borelOf L S).subgroupOf L).index = 5 := by
  obtain ⟨hp, hodd, hmap⟩ := F1.map_borelOf_eq_normalizer hsyl
  set π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L) with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ (borelOf L S).subgroupOf L := by
    rw [hπ, QuotientGroup.ker_mk']
    intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 L := (F1.mem_pCore_iff_coe x).mp hx
    exact F1.sylow_le_borelOf L S (isSylowTwoOf_pCoreOf_le hsyl h1)
  rw [← Subgroup.index_map_eq _ hsurj hker, hmap]
  set Tb : Subgroup (oTwoQuot ↥L) := Subgroup.map π ((S ⊓ L).subgroupOf L) with hTb
  have hT' : IsPGroup 2 (Tb.map e.toMonoidHom) := hp.map e.toMonoidHom
  have hodd' : ¬ 2 ∣ (Tb.map e.toMonoidHom).index := by
    rw [show e.toMonoidHom = (e : oTwoQuot ↥L →* Alt5) from rfl, Subgroup.index_map_equiv]
    exact hodd
  have h5 := index_normalizer_sylow_alt5 hT' hodd'
  rw [← Subgroup.map_normalizer_eq_of_bijective Tb e.bijective,
    show e.toMonoidHom = (e : oTwoQuot ↥L →* Alt5) from rfl, Subgroup.index_map_equiv] at h5
  exact h5

omit [Finite G] in
theorem card_oTwoQuot_alt5 (e : OTwoQuot L ≃* Alt5) : Nat.card (OTwoQuot L) = 2 ^ 2 * 15 := by
  rw [Nat.card_congr e.toEquiv, a5_card]
  norm_num

theorem index_sylow_of_alt5 (hsyl : IsSylowTwoOf (S ⊓ L) L) (e : OTwoQuot L ≃* Alt5) :
    ((S ⊓ L).subgroupOf L).index = 15 :=
  index_sylow_eq_of_card_quot hsyl (by decide) (card_oTwoQuot_alt5 e)

theorem exists_cartan_three (hsyl : IsSylowTwoOf (S ⊓ L) L) (e : OTwoQuot L ≃* Alt5) :
    ∃ D : Subgroup G, D ≤ borelOf L S ∧ Nat.card D = 3 ∧ D ⊓ (S ⊓ L) = ⊥ ∧
      (S ⊓ L) ⊔ D = borelOf L S := by
  obtain ⟨D, ⟨hDB, -, -⟩, hDS, hsup⟩ := F1.exists_cartan (Lj := L) (S := S) hsyl
  refine ⟨D, hDB, ?_, hDS, hsup⟩
  have h5 : (borelOf L S).relIndex L = 5 := index_borelOf_of_alt5 hsyl e
  have h15 : (S ⊓ L).relIndex L = 15 := index_sylow_of_alt5 hsyl e
  have hmul := Subgroup.relIndex_mul_relIndex (S ⊓ L) (borelOf L S) L
    (F1.sylow_le_borelOf L S) (F1.borelOf_le L S)
  rw [h5, h15] at hmul
  have h3 : (S ⊓ L).relIndex (borelOf L S) = 3 := by omega
  have hnorm : D ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    hDB.trans (F1.borelOf_le_normalizer L S)
  have hrel := F1.relIndex_sup_eq_of_le_normalizer hnorm
  rw [sup_comm, hsup, h3] at hrel
  rw [← Subgroup.inf_relIndex_right, inf_comm, hDS, Subgroup.relIndex_bot_left] at hrel
  exact hrel.symm

end FA5

end CFSG.Quasithin
