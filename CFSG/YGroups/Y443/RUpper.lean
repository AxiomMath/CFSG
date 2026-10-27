module

public import CFSG.YGroups.Y443.RIntersection
public import CFSG.YGroups.DCE.B433FixCheck

public section

namespace CFSG.YGroups.Y443Edge

open CFSG.Open (MonsterY443Derived)
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

@[expose] noncomputable def qp : Q343 :=
  Q343.π ((yGen 3 4 3 0 * yGen 3 4 3 4 * yGen 3 4 3 5 * yGen 3 4 3 6 * yGen 3 4 3 1 *
    yGen 3 4 3 2 * yGen 3 4 3 8) ^ 9)

theorem y443Q343Hom_qp :
    y443Q343Hom qp = y443C' := by
  rw [qp, y443C'_eq_pow, map_pow, map_pow]
  simp only [map_mul, y443Q343Hom_gen (show 0 < 11 by norm_num),
    y443Q343Hom_gen (show 4 < 11 by norm_num), y443Q343Hom_gen (show 5 < 11 by norm_num),
    y443Q343Hom_gen (show 6 < 11 by norm_num), y443Q343Hom_gen (show 1 < 11 by norm_num),
    y443Q343Hom_gen (show 2 < 11 by norm_num), y443Q343Hom_gen (show 8 < 11 by norm_num)]
  rfl

theorem beta_qp :
    beta qp = DCE.B433.psi DCE.B433.dY := by
  have hg : ∀ c < 11, cyc343Letter c < 10 →
      beta (Q343.π (yGen 3 4 3 c)) = DCE.B433.psi (yGen 4 3 2 (cyc343Letter c)) := by
    intro c hc hc'
    rw [beta_gen hc, DCE.B433.psi, MonoidHom.comp_apply, DCE.B433.psiU_yGen hc']
  rw [qp, DCE.B433.dY, map_pow, map_pow, map_pow]
  congr 1
  simp only [map_mul, hg 0 (by norm_num) (by decide), hg 4 (by norm_num) (by decide),
    hg 5 (by norm_num) (by decide), hg 6 (by norm_num) (by decide),
    hg 1 (by norm_num) (by decide), hg 2 (by norm_num) (by decide),
    hg 8 (by norm_num) (by decide)]
  simp only [DCE.B433.dWord, List.toList_toArray, evalWord_cons, evalWord_nil, mul_one, map_mul,
    ← mul_assoc]
  rfl

theorem card_centralizer_qp_le
    (hqc : qc ≠ 1) {g : Q343} (hg : g * qp * g⁻¹ = qp * qc) :
    Nat.card (Subgroup.centralizer {qp}) ≤ Nat.card (Subgroup.centralizer {beta qp}) := by
  classical
  have := YGroups.Q343_finite_card_le.1
  set Z := Subgroup.centralizer {qp} with hZ
  set C := Subgroup.centralizer {beta qp} with hC
  set Z' := C.comap beta with hZ'
  have := YGroups.B433_finite_card_le.1
  have hbqc : beta qc = 1 := by
    have h : qc ∈ beta.ker := by
      rw [ker_beta]
      exact Subgroup.mem_zpowers qc
    exact MonoidHom.mem_ker.1 h
  have hle : Z ≤ Z' := by
    intro z hz
    rw [hZ', Subgroup.mem_comap, hC, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      (Subgroup.mem_centralizer_singleton_iff.1 hz)]
  have hgZ' : g ∈ Z' := by
    rw [hZ', Subgroup.mem_comap, hC, Subgroup.mem_centralizer_singleton_iff]
    have h1 := congrArg beta hg
    rw [map_mul, map_mul, map_inv, map_mul, hbqc, mul_one] at h1
    calc beta g * beta qp = beta g * beta qp * (beta g)⁻¹ * beta g := by group
      _ = beta qp * beta g := by rw [h1]
  have hgZ : g ∉ Z := by
    intro hgz
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hgz
    have : qp * qc = qp := by
      rw [← hg, h1, mul_assoc, mul_inv_cancel, mul_one]
    exact hqc (mul_left_cancel (a := qp) (by rw [this, mul_one]))
  have hmul := Subgroup.relIndex_mul_card (H := Z) (K := Z')
  rw [inf_of_le_left hle] at hmul
  have hidx : 2 ≤ Z.relIndex Z' := by
    have h0 : Z.relIndex Z' ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hmul
      exact (Nat.card_pos (α := Z')).ne' hmul.symm
    have h1 : Z.relIndex Z' ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      exact fun h => hgZ (h hgZ')
    omega
  have hkerle : beta.ker ≤ Z' := by
    intro k hk
    rw [hZ', Subgroup.mem_comap, MonoidHom.mem_ker.1 hk]
    exact C.one_mem
  have hcardker : Nat.card beta.ker = 2 := by
    rw [ker_beta, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two, qc_mul_self]) hqc
  have hZ'card : Nat.card Z' = 2 * Nat.card C := by
    have h1 := Subgroup.card_ker_mul_card_range (beta.domRestrict Z')
    rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range,
      Subgroup.map_comap_eq_self_of_surjective beta_surjective] at h1
    rw [← h1, (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv).trans hcardker]
  have hCpos : 0 < Nat.card C := Nat.card_pos
  rw [hZ'card] at hmul
  nlinarith

variable {G : Type*} [Group G] (f : MonsterY443Derived →* G)

theorem qc_ne_one
    (hN : Q343N ≤ Nat.card (y443H.map f)) : qc ≠ 1 := by
  have := YGroups.Q343_finite_card_le.1
  intro h1
  have hinj : Function.Injective beta := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_beta, h1, Subgroup.zpowers_one_eq_bot]
  have h2 : Nat.card Q343 ≤ Nat.card B433 := by
    have := YGroups.B433_finite_card_le.1
    exact Nat.card_le_card_of_injective _ hinj
  have h3 : Q343N ≤ Nat.card Q343 := by
    have := Nat.card_le_card_of_surjective _ (rho f).rangeRestrict_surjective
    rw [range_rho] at this
    exact hN.trans this
  have h4 := YGroups.B433_finite_card_le.2
  have hQ : Q343N = 2 * 4154781481226426191177580544000000 := by unfold Q343N; norm_num
  omega

theorem inf_map_le_map_centralizer
    (hN : Q343N ≤ Nat.card (y443H.map f)) :
    y443H.map f ⊓ y443H'.map f ≤ (Subgroup.centralizer {qp}).map (rho f) := by
  rintro u ⟨hu, ⟨h', hh', rfl⟩⟩
  rw [← range_rho] at hu
  obtain ⟨q, hq⟩ := hu
  refine ⟨q, ?_, hq⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  apply rho_injective f hN
  have hc : f h' * f y443C' = f y443C' * f h' := by
    rw [← map_mul, ← map_mul, y443C'_comm_H' hh']
  have hρ : rho f qp = f y443C' := by
    rw [rho, MonoidHom.comp_apply, y443Q343Hom_qp]
  rw [map_mul, map_mul, hq, hρ, hc]

theorem inf_map_eq_of_conj
    (hN : Q343N ≤ Nat.card (y443H.map f)) {g : Q343}
    (hg : g * qp * g⁻¹ = qp * qc) : y443H.map f ⊓ y443H'.map f = y443R.map f := by
  classical
  have := YGroups.Q343_finite_card_le.1
  have hfin : Finite (y443H.map f) := by
    rw [← range_rho]
    exact Set.finite_range _ |>.to_subtype
  have hle : y443R.map f ≤ y443H.map f ⊓ y443H'.map f :=
    le_inf (Subgroup.map_mono y443R_le_H) (Subgroup.map_mono y443R_le_H')
  have hfin' : Finite (y443H.map f ⊓ y443H'.map f : Subgroup G) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left :
      y443H.map f ⊓ y443H'.map f ≤ y443H.map f))
  have hfinC : Finite ((Subgroup.centralizer {qp}).map (rho f)) :=
    Finite.of_surjective (fun x : Subgroup.centralizer {qp} =>
      (⟨rho f x, Subgroup.mem_map_of_mem _ x.2⟩ : (Subgroup.centralizer {qp}).map (rho f)))
      (by rintro ⟨_, ⟨y, hy, rfl⟩⟩; exact ⟨⟨y, hy⟩, rfl⟩)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  calc Nat.card (y443H.map f ⊓ y443H'.map f : Subgroup G)
      ≤ Nat.card ((Subgroup.centralizer {qp}).map (rho f)) :=
        Subgroup.card_le_of_le (inf_map_le_map_centralizer f hN)
    _ = Nat.card (Subgroup.centralizer {qp}) :=
        Subgroup.card_map_of_injective (rho_injective f hN)
    _ ≤ Nat.card (Subgroup.centralizer {beta qp}) :=
        card_centralizer_qp_le (qc_ne_one f hN) hg
    _ ≤ 306129918735099415756800 := by
        rw [beta_qp]
        exact DCE.B433.card_centralizer_dY_le (card_B433_ge f hN)
    _ ≤ Nat.card (y443R.map f) := card_map_y443R_ge f hN

end CFSG.YGroups.Y443Edge
