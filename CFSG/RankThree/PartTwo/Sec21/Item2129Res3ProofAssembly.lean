module

public import CFSG.RankThree.PartTwo.Sec21.Item2129Res2ProofAssembly
public import CFSG.RankThree.PartTwo.Sec21.Item2119End5ProofPair
import CFSG.RankThree.PartTwo.Sec21.Item2129Res3ProofComm
import CFSG.RankThree.PartTwo.Sec21.Item2129Res3ProofOdd
import CFSG.RankThree.PartTwo.Sec21.Item2129Res3ProofL34

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Item2129LQuasi : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ Lf : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) →
        Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)) →
        ∀ e ∈ A, e ∉ Subgroup.zpowers d → CFSG.IsQuasisimple (Lf e)

namespace Item2129Res3Proof

open Item2129Res2Proof

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_of_comm {Le : Subgroup G} {e g : G} (hLe : Le ∈ thetaComponentsAt 3 e)
    (h3 : 3 ∣ Nat.card Le) (huniq : ∀ K ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card K → K = Le)
    (hge : g * e = e * g) {l : G} (hl : l ∈ Le) : g * l * g⁻¹ ∈ Le := by
  have h1 := CFSG.RankThree.PartTwo.map_mem_thetaComponentsAt (MulAut.conj g) hLe
  have hge' : MulAut.conj g e = e := by
    rw [MulAut.conj_apply, hge, mul_inv_cancel_right]
  rw [hge'] at h1
  have hcard : 3 ∣ Nat.card (Le.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact h3
  have heq := huniq _ h1 hcard
  have hmem : g * l * g⁻¹ ∈ Le.map (MulAut.conj g).toMonoidHom := ⟨l, hl, rfl⟩
  rwa [heq] at hmem

theorem exists_two_pow_inv {H : Subgroup G} {t₀ : G} (ht₀ : ∀ h ∈ H, t₀ * h * t₀⁻¹ = h⁻¹) :
    ∃ u m : ℕ, (t₀ ^ u) ^ 2 ^ m = 1 ∧ ∀ h ∈ H, t₀ ^ u * h * (t₀ ^ u)⁻¹ = h⁻¹ := by
  have hn : orderOf t₀ ≠ 0 := (orderOf_pos t₀).ne'
  obtain ⟨m, u, hu, hmu⟩ := Nat.exists_eq_two_pow_mul_odd hn
  refine ⟨u, m, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, ← hmu, pow_orderOf_eq_one]
  · have heven : ∀ j : ℕ, ∀ h ∈ H, t₀ ^ (2 * j) * h * (t₀ ^ (2 * j))⁻¹ = h := by
      intro j
      induction j with
      | zero => intro h _; group
      | succ j ih =>
        intro h hh
        have h1 : t₀ ^ (2 * (j + 1)) = t₀ * t₀ * t₀ ^ (2 * j) := by
          rw [show 2 * (j + 1) = 2 + 2 * j by ring, pow_add, pow_two]
        rw [h1]
        calc t₀ * t₀ * t₀ ^ (2 * j) * h * (t₀ * t₀ * t₀ ^ (2 * j))⁻¹
            = t₀ * (t₀ * (t₀ ^ (2 * j) * h * (t₀ ^ (2 * j))⁻¹) * t₀⁻¹) * t₀⁻¹ := by group
          _ = t₀ * (t₀ * h * t₀⁻¹) * t₀⁻¹ := by rw [ih h hh]
          _ = t₀ * h⁻¹ * t₀⁻¹ := by rw [ht₀ h hh]
          _ = h := by rw [ht₀ _ (H.inv_mem hh), inv_inv]
    obtain ⟨j, rfl⟩ := hu
    intro h hh
    calc t₀ ^ (2 * j + 1) * h * (t₀ ^ (2 * j + 1))⁻¹
        = t₀ ^ (2 * j) * (t₀ * h * t₀⁻¹) * (t₀ ^ (2 * j))⁻¹ := by rw [pow_succ]; group
      _ = t₀ ^ (2 * j) * h⁻¹ * (t₀ ^ (2 * j))⁻¹ := by rw [ht₀ h hh]
      _ = (t₀ ^ (2 * j) * h * (t₀ ^ (2 * j))⁻¹)⁻¹ := by group
      _ = h⁻¹ := by rw [heven j h hh]

theorem comm_of_quasi {F Q Y Le : Subgroup G} {e d : G} (hL : Loc2129 F (F ⊓ Le) Q Y e d)
    (hLe : Le ∈ thetaComponentsAt 3 e) (h3L : 3 ∣ Nat.card Le)
    (huniq : ∀ K ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card K → K = Le)
    (hq : CFSG.IsQuasisimple Le) (ψ : lBar Le ≃* projSL 3 (GaloisField 2 2))
    (hNY : Le ⊓ Subgroup.normalizer (F : Set G) ≤ Y)
    (hodd : Odd (Nat.card (Y ⊓ Subgroup.centralizer (F : Set G) : Subgroup G)))
    {t : G} (htL : t ∈ Le) (htN : t ∈ Subgroup.normalizer (F : Set G)) {m : ℕ}
    (ht2 : t ^ 2 ^ m = 1) (htH : ∀ h ∈ F ⊓ Le, t * h * t⁻¹ = h⁻¹) :
    ∀ o ∈ Y ⊓ Subgroup.centralizer (F : Set G), Nat.Coprime (orderOf o) 3 → t * o = o * t := by
  intro o ho ho3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLC : Le ≤ Subgroup.centralizer ({e} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLe
  have hoe : o * e = e * o := (Subgroup.mem_centralizer_iff.mp ho.2 e hL.mem_e).symm
  have hoinve : o⁻¹ * e = e * o⁻¹ := by
    calc o⁻¹ * e = o⁻¹ * (e * o) * o⁻¹ := by group
      _ = o⁻¹ * (o * e) * o⁻¹ := by rw [hoe]
      _ = e * o⁻¹ := by group
  have hotL : o⁻¹ * t * o ∈ Le := by
    have h := conj_mem_of_comm hLe h3L huniq hoinve htL
    rwa [inv_inv] at h
  have huL : o⁻¹ * (t * o * t⁻¹) ∈ Le := by
    rw [show o⁻¹ * (t * o * t⁻¹) = (o⁻¹ * t * o) * t⁻¹ by group]
    exact Le.mul_mem hotL (Le.inv_mem htL)
  have htY : t ∈ Y := hNY ⟨htL, htN⟩
  have htoC := conj_mem_C hL htY ho
  have huF : o⁻¹ * (t * o * t⁻¹) ∈ Subgroup.centralizer (F : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ ho.2) htoC.2
  have huH : o⁻¹ * (t * o * t⁻¹) ∈ Subgroup.centralizer ((F ⊓ Le : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (show ((F ⊓ Le : Subgroup G) : Set G) ⊆ F from fun x hx => hx.1) huF
  have hH3 : IsPGroup 3 (F ⊓ Le : Subgroup G) := Loc2129.isPGroup_of_pow hL.pow_H
  obtain ⟨h, hh, hz⟩ := exists_mem_inv_mul_mem_theta ψ inf_le_right hL.card_H hH3 huL huH
  have hTne : aschbacherSolvableCore 3 Le ≠ ⊤ := by
    intro hT
    apply (solvable_prime_complement_core_characterization (H := Le) Nat.prime_three).2.2.1
    rw [hT, Subgroup.card_top]
    exact h3L
  have hcen : aschbacherSolvableCore 3 Le ≤ Subgroup.center Le :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top
      ⟨hq.1.commutator_eq_top, hq.2.1⟩ _ hTne
  set z := h⁻¹ * (o⁻¹ * (t * o * t⁻¹)) with hzdef
  have hzc : ∀ l ∈ Le, l * z = z * l := by
    intro l hl
    obtain ⟨z', hz', hzz'⟩ := hz
    have hz'c := Subgroup.mem_center_iff.mp (hcen hz') ⟨l, hl⟩
    rw [← hzz']
    exact congrArg Subtype.val hz'c
  have hhF : h ∈ F := hh.1
  have hhL : h ∈ Le := hh.2
  have hzL : z ∈ Le := Le.mul_mem (Le.inv_mem hhL) huL
  have hhC : h ∈ Subgroup.centralizer ((F ⊓ Le : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => hL.comm_F x hx.1 h hhF
  have hzH : z ∈ Subgroup.centralizer ((F ⊓ Le : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hhC) huH
  have hze : z * e = e * z := Subgroup.mem_centralizer_singleton_iff.mp (hLC hzL)
  have hzF : z ∈ Subgroup.centralizer (F : Set G) := hL.mem_centralizer_F hzH hze
  have hzN : z ∈ Subgroup.normalizer (F : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun f hf => ?_
    have h1 : f * z = z * f := Subgroup.mem_centralizer_iff.mp hzF f hf
    rw [show z * f * z⁻¹ = f by rw [← h1]; group]
    exact hf
  have hzC : z ∈ Y ⊓ Subgroup.centralizer (F : Set G) := ⟨hNY ⟨hzL, hzN⟩, hzF⟩
  have hzodd : Odd (orderOf z) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hzC)
  have hto : t * o * t⁻¹ = o * h * z := by rw [hzdef]; group
  have hth : t * h * t⁻¹ = h⁻¹ := htH h hh
  have htz : t * z = z * t := hzc t htL
  have htz' : t * z * t⁻¹ = z := by rw [htz]; group
  have hhz : h * z = z * h := hzc h hhL
  have ht2o : t ^ 2 * o * (t ^ 2)⁻¹ = o * z ^ 2 := by
    calc t ^ 2 * o * (t ^ 2)⁻¹ = t * (t * o * t⁻¹) * t⁻¹ := by rw [pow_two]; group
      _ = t * (o * h * z) * t⁻¹ := by rw [hto]
      _ = (t * o * t⁻¹) * (t * h * t⁻¹) * (t * z * t⁻¹) := by group
      _ = (o * h * z) * h⁻¹ * z := by rw [hto, hth, htz']
      _ = o * (h * z) * h⁻¹ * z := by group
      _ = o * (z * h) * h⁻¹ * z := by rw [hhz]
      _ = o * z ^ 2 := by rw [pow_two]; group
  have hiter : ∀ k : ℕ, t ^ (2 * k) * o * (t ^ (2 * k))⁻¹ = o * z ^ (2 * k) := by
    intro k
    induction k with
    | zero => group
    | succ k ih =>
      have hc : Commute (t ^ 2) (z ^ (2 * k)) := Commute.pow_pow (show Commute t z from htz) 2 _
      have htzk : t ^ 2 * z ^ (2 * k) * (t ^ 2)⁻¹ = z ^ (2 * k) := by
        rw [hc.eq]
        group
      calc t ^ (2 * (k + 1)) * o * (t ^ (2 * (k + 1)))⁻¹
          = t ^ 2 * (t ^ (2 * k) * o * (t ^ (2 * k))⁻¹) * (t ^ 2)⁻¹ := by
            rw [show 2 * (k + 1) = 2 + 2 * k by ring, pow_add]
            group
        _ = t ^ 2 * (o * z ^ (2 * k)) * (t ^ 2)⁻¹ := by rw [ih]
        _ = (t ^ 2 * o * (t ^ 2)⁻¹) * (t ^ 2 * z ^ (2 * k) * (t ^ 2)⁻¹) := by group
        _ = o * z ^ 2 * z ^ (2 * k) := by rw [ht2o, htzk]
        _ = o * z ^ (2 * (k + 1)) := by
            rw [show 2 * (k + 1) = 2 + 2 * k by ring, pow_add]
            group
  have hz1 : z = 1 := by
    have h1 := hiter (2 ^ m)
    have ht : t ^ (2 * 2 ^ m) = 1 := by rw [mul_comm, pow_mul, ht2, one_pow]
    rw [ht, one_mul, inv_one, mul_one] at h1
    have h2 : z ^ (2 * 2 ^ m) = 1 := mul_eq_left.mp h1.symm
    have h3 : orderOf z ∣ 2 ^ (m + 1) := by
      rw [pow_succ']
      exact orderOf_dvd_of_pow_eq_one h2
    obtain ⟨j, -, hjz⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    rcases j with _ | j
    · rwa [pow_zero, orderOf_eq_one_iff] at hjz
    · exfalso
      rw [hjz] at hzodd
      exact (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, by omega⟩)) hzodd
  have hto' : t * o * t⁻¹ = o * h := by rw [hto, hz1, mul_one]
  have hoh : o * h = h * o := (Subgroup.mem_centralizer_iff.mp ho.2 h hhF).symm
  have hh1 : h = 1 := by
    have hs : SemiconjBy t o (t * o * t⁻¹) := by
      unfold SemiconjBy
      group
    have hord : orderOf (o * h) = orderOf o := by
      rw [← hto', ← SemiconjBy.orderOf_eq t hs]
    have h1 : (o * h) ^ orderOf o = 1 := by
      rw [← hord]
      exact pow_orderOf_eq_one _
    rw [Commute.mul_pow (show Commute o h from hoh), pow_orderOf_eq_one, one_mul] at h1
    have h2 : orderOf h ∣ orderOf o := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf h ∣ 3 := orderOf_dvd_of_pow_eq_one (hL.pow_F h hhF)
    have h4 : orderOf h ∣ Nat.gcd (orderOf o) 3 := Nat.dvd_gcd h2 h3
    rw [ho3.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h4
    exact h4
  calc t * o = t * o * t⁻¹ * t := by group
    _ = o * t := by rw [hto', hh1, mul_one]

end Item2129Res3Proof

open Item2129Res3Proof

theorem item2129SO_of_quasi (hQ : Item2129LQuasi) : Item2129SO := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ' hQX h28 e he hed
  have hL := Item2129Res2Proof.loc2129_of hE hLf h26 hF h27 hQ' hQX h28 he hed
  have hrank : CFSG.Assembly.RankThreeEven.localRank 3 G ≤ 3 :=
    hE.cfg.pair.standing.toTheoremFourHyp.localRank_three.le
  have hodd := odd_card_centralizer hL hrank
  have hq := hQ G A E U c L d U₀ a X hE h23 h24 Lf hLf h26 e he hed
  obtain ⟨hLe, h3L, huniq, ⟨eLe⟩, -⟩ := hLf e he hed
  obtain ⟨eL⟩ := h26
  obtain ⟨t₀, ⟨ht₀L, ht₀N⟩, ht₀H⟩ :=
    Item2129Res2Proof.exists_inv_of (hF e he hed) (hLf e he hed) ⟨eL⟩ (h28 e he hed)
  obtain ⟨u, m, ht2, htH⟩ := exists_two_pow_inv ht₀H
  have htL : t₀ ^ u ∈ Lf e := Subgroup.pow_mem _ ht₀L u
  have htN : t₀ ^ u ∈ Subgroup.normalizer (F e : Set G) := Subgroup.pow_mem _ ht₀N u
  have hNY : Lf e ⊓ Subgroup.normalizer (F e : Set G) ≤ y2128Of (Lf e) (F e) (q2127Of A d F) :=
    le_sup_left
  exact comm_of_inv hL (hNY ⟨htL, htN⟩) htH
    (comm_of_quasi hL hLe h3L huniq hq (eLe.trans eL) hNY hodd htL htN ht2 htH)

section Certs

theorem item2129LQuasi_of (h211 : Item211) (h2115 : Item2115) (h2116 : Item2116)
    (h218 : Item218) (h2118 : Item2118) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h66 : Sec6.Item6_6) (hStar : Item2125Star) (h213 : Item213) : Item2129LQuasi := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf h26 e he hed
  obtain ⟨U', hp⟩ :=
    exists_pair2127 h211 h2115 h2116 h218 h2118 h45 h48 h66 hStar hE h23 h24 hLf h26 he hed
  exact h213 G A E U' e (Lf e) hp.cfg.pair

theorem item2129SO_of_items (h211 : Item211) (h2115 : Item2115) (h2116 : Item2116)
    (h218 : Item218) (h2118 : Item2118) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h66 : Sec6.Item6_6) (hStar : Item2125Star) (h213 : Item213) : Item2129SO :=
  item2129SO_of_quasi
    (item2129LQuasi_of h211 h2115 h2116 h218 h2118 h45 h48 h66 hStar h213)

theorem item2129S_of_items (h211 : Item211) (h2115 : Item2115) (h2116 : Item2116)
    (h218 : Item218) (h2118 : Item2118) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h66 : Sec6.Item6_6) (hStar : Item2125Star) (h213 : Item213) : Item2129S :=
  item2129S_of_so (item2129SO_of_items h211 h2115 h2116 h218 h2118 h45 h48 h66 hStar h213)

theorem item2129S_of_itemsLocal (h211 : Item211) (h2115 : Item2115) (h2116 : Item2116)
    (h218 : Item218) (h2118 : Item2118) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h66 : Sec6.Item6_6) (hLoc : Item2125StarLocal) (h213 : Item213) : Item2129S :=
  item2129S_of_items h211 h2115 h2116 h218 h2118 h45 h48 h66 (item2125Star_of_local h45 h66 hLoc)
    h213

end Certs

end CFSG.RankThree.PartTwo.Sec21
