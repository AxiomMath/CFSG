module

public import CFSG.Quasithin.Vol2.Ch9KGFFR
public import CFSG.Quasithin.Vol2.Ch9KGFFNq
public import CFSG.Quasithin.Vol2.Ch9KGFFOff
public import CFSG.Quasithin.Vol2.Ch9Sec3FFBBar

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_modO2Image
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (h314 : A314Facts) (h56 : AsB56)
    {Y T K KY U : Subgroup G} (hSQ : SQTKGroup ↥Y) (hT : IsSylowTwoOf T Y) (hKY : K ≤ Y)
    (hKl : K ∈ lFamily T) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hA5 : Nonempty (O2Q K ≃* alternatingGroup (Fin 5))) (hKYc : KY ∈ cComp Y) (hlt : K < KY)
    (hYKY : Y ≤ Subgroup.normalizer (KY : Set G)) (hred : IsTwoReducedIn Y U)
    (hJ : ¬ ⁅KY, thompsonJ T⁆ ≤ Subgroup.centralizer (U : Set G))
    (hnK : ¬ KY ≤ K ⊔ (KY ⊓ Subgroup.centralizer (U : Set G)))
    (hKU : ¬ K ≤ Subgroup.centralizer (U : Set G)) :
    CFSG.IsQuasisimple ↥(modO2Image Y KY) := by
  by_contra hnq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsMulCommutative ↥U := hred.2.2.1.1
  have hVe : IsElemAbelian 2 U := hred.2.2.1
  have hV : ∀ v : ↥U, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hVe.2 v v.2)
  have hYU : Y ≤ Subgroup.normalizer (U : Set G) := hred.2.1
  have hKYY : KY ≤ Y := le_of_mem_cComp hKYc
  have hKYN : KY ≤ Subgroup.normalizer (U : Set G) := hKYY.trans hYU
  have hKN : K ≤ Subgroup.normalizer (U : Set G) := hlt.le.trans hKYN
  have hperf : ⁅KY, KY⁆ = KY := perfect_of_mem_cComp hKYc
  have hKperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hKl
  have hO2 : pCoreOf 2 (autOn Y U) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  obtain ⟨-, h314bar⟩ := FFB.a314_bar h36 h312 h314 hSQ hT hKY hKl hTK hA5 hKYc hlt
  have hQbar := SQTKHyp.of_sqtkGroup ↥Y hSQ
  have hstrong : A36Strong (modO2Image Y KY) := h36 _ hQbar _ (modO2Image_mem_cComp hKYc)
  have h1314 := a314_nonquasi h314 hstrong hnq h314bar
  obtain ⟨hOn, hOodd, hO3, hOq⟩ := oddCore_facts hstrong hnq
  set KYs := autOn KY U with hKYs
  set Ys := autOn Y U with hYs
  set ψ := psi hKYY hred with hψ
  set R' := (CFSG.oddCore ↥(modO2Image Y KY)).map ψ with hR'
  set Rs := rStar hKYY hred with hRs
  have hR'n : R'.Normal := Subgroup.Normal.map inferInstance ψ (psi_surjective hKYY hred)
  have hKYX : KYs ≤ Ys := InternalSec.autOn_le_autOn_of_le hKYY
  have hXKY : Ys ≤ Subgroup.normalizer (KYs : Set (MulAut ↥U)) := by
    refine le_normalizer_of_conj fun x hx k hk => ?_
    exact InternalSec.autOn_normal_of (U := U) hYKY x hx k hk
  have hXR : Ys ≤ Subgroup.normalizer (Rs : Set (MulAut ↥U)) := le_normalizer_rStar hKYY hred hYKY
  have hperfA : ⁅KYs, KYs⁆ = KYs := FFD.perfect_autOn hKYN hperf
  have hRn : Group.IsNilpotent ↥Rs := isNilpotent_rStar hKYY hred hOn
  have hRdvd := card_rStar_dvd hKYY hred
  have hRodd : Odd (Nat.card ↥Rs) := Odd.of_dvd_nat hOodd hRdvd
  have hR3 : ¬ 3 ∣ Nat.card ↥Rs := fun h3 => hO3 (h3.trans hRdvd)
  have hR'card : Nat.card ↥R' = Nat.card ↥Rs := by
    rw [hRs, rStar, Subgroup.card_map_of_injective (autOn KY U).subtype_injective]
  have h60 : 60 ∣ Nat.card ↥KYs :=
    (FFD.card_autOn_dvd hKN hKperf hA5 hKU).trans
      (Subgroup.card_dvd_of_le (InternalSec.autOn_le_autOn_of_le hlt.le))
  set Q := ↥KYs ⧸ R' with hQ
  set f := QuotientGroup.mk' R' with hf
  have hfs : Function.Surjective f := QuotientGroup.mk'_surjective R'
  have hker : f.ker = Rs.subgroupOf KYs := by
    rw [hf, QuotientGroup.ker_mk', hRs, rStar_subgroupOf]
  have hle : CFSG.oddCore ↥(modO2Image Y KY) ≤ R'.comap ψ := Subgroup.le_comap_map _ _
  set σ := QuotientGroup.map _ R' ψ hle with hσ
  have hσs : Function.Surjective σ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R' q
    obtain ⟨l, rfl⟩ := psi_surjective hKYY hred x
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hRne : R' ≠ ⊤ := by
    intro htop
    have h1 : Nat.card ↥R' = Nat.card ↥KYs := by rw [htop, Subgroup.card_top]
    rw [hR'card] at h1
    rw [← h1] at h60
    exact (Nat.not_even_iff_odd.mpr hRodd) (even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 60).trans h60))
  have hσne : ∃ k, σ k ≠ 1 := by
    obtain ⟨x, hx⟩ : ∃ x : ↥KYs, x ∉ R' := by
      by_contra hcon
      push Not at hcon
      exact hRne (eq_top_iff.mpr fun x _ => hcon x)
    obtain ⟨l, rfl⟩ := psi_surjective hKYY hred x
    refine ⟨QuotientGroup.mk l, ?_⟩
    show (QuotientGroup.mk (ψ l) : Q) ≠ 1
    rwa [Ne, QuotientGroup.eq_one_iff]
  have hQq : CFSG.IsQuasisimple Q :=
    CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hOq hσs hσne
  rcases ffJ_dichotomy hV hKYX hXKY hXR hperfA hRn hRodd hR3 hQq f hfs hker with hc | ⟨hKJ, hcen⟩
  · exact hJ (commutator_le_centralizer_of_ffJ hVe hred hT hKYY hc)
  have hqA : CFSG.IsQuasisimple ↥KYs := isQuasisimple_of_central hperfA hcen hQq f hfs hker
  obtain ⟨A, -, hA, hLA⟩ := FFD.exists_offender_of_commutator hVe hred hT hKYY hYKY hqA le_rfl hJ
  have hV2 : ∀ w ∈ U, w ^ 2 = 1 := fun w hw => by simpa [pow_two] using hVe.2 w hw
  obtain ⟨hKJ', -, -, -, hcases⟩ :=
    InternalSec.b56Cases_ffJ_autOn h56 hV2 hYU hKYY hYKY hSQ hO2 hA hLA
  have hsnX : IsSubnormal (autOn KY U) (autOn Y U) :=
    A3.subnormal_map (conjAct U)
      (A3.subnormal_comap (Subgroup.normalizer (U : Set G)).subtype (subnormal_of_mem_cComp hKYc))
  have hlist := SBc3.b56QL_of_subnormal hKJ' (A3.subnormal_of_le_of_le hsnX hKJ' (B6.ffJ_le _))
    hqA hcases
  rcases h1314 with ⟨-, h13⟩ | ⟨-, p, hp, hp5, hp8, hpSL⟩
  ·
    apply hnK
    set Lb := modO2Image Y KY with hLb
    set Ob := oddCoreSub Lb with hOb
    have hKbL : modO2Image Y K ≤ Lb := Subgroup.map_mono fun x hx => hlt.le hx
    have hKbO : modO2Image Y K ≤ Subgroup.normalizer (Ob : Set (↥Y ⧸ CFSG.pCore 2 ↥Y)) := by
      refine le_normalizer_of_conj fun b hb o ho => ?_
      obtain ⟨o', ho', rfl⟩ := ho
      have hbL := hKbL hb
      refine ⟨⟨b, hbL⟩ * o' * ⟨b, hbL⟩⁻¹, ?_, rfl⟩
      exact (inferInstance : (CFSG.oddCore ↥Lb).Normal).conj_mem _ ho' _
    have hsup : KYs ≤ autOn K U ⊔ Rs := by
      intro x hx
      obtain ⟨k, hk⟩ := InternalSec.autOnHom_surjective hKYN ⟨x, hx⟩
      have hkL : (barMap hKYY k : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ Ob ⊔ modO2Image Y K := by
        rw [sup_comm, ← h13]
        exact (barMap hKYY k).2
      obtain ⟨o, ho, b, hb, hob⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hKbO).1 hkL
      obtain ⟨b', hb', rfl⟩ := hb
      have hbK : ((b' : ↥Y) : G) ∈ K := hb'
      set kb : ↥KY := ⟨(b' : G), hlt.le hbK⟩ with hkb
      set k₁ : ↥KY := k * kb⁻¹ with hk₁
      have hbar1 : ((barMap hKYY kb : ↥Lb) : ↥Y ⧸ CFSG.pCore 2 ↥Y) =
          QuotientGroup.mk' (CFSG.pCore 2 ↥Y) b' := rfl
      have hbar2 : ((barMap hKYY k₁ : ↥Lb) : ↥Y ⧸ CFSG.pCore 2 ↥Y) = o := by
        rw [hk₁, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hbar1, hob]
        group
      obtain ⟨o', ho', ho'o⟩ := ho
      have hk₁O : barMap hKYY k₁ ∈ CFSG.oddCore ↥Lb := by
        have : barMap hKYY k₁ = o' := Subtype.ext (by rw [hbar2, ← ho'o]; rfl)
        rw [this]
        exact ho'
      have hx' : x = ((InternalSec.autOnHom hKYN k₁ : ↥KYs) : MulAut ↥U) *
          ((InternalSec.autOnHom hKYN kb : ↥KYs) : MulAut ↥U) := by
        rw [← Subgroup.coe_mul, ← map_mul, hk₁, inv_mul_cancel_right, hk]
      rw [hx', sup_comm]
      refine Subgroup.mul_mem_sup ?_ ?_
      · exact ⟨InternalSec.autOnHom hKYN k₁, ⟨_, hk₁O, psi_barMap hKYY hred k₁⟩, rfl⟩
      · exact Setup.mem_autOn_iff.2 ⟨Subgroup.inclusion hKYN kb, hbK, rfl⟩
    have hJR : ∀ j ∈ autOn K U, ∀ r ∈ Rs, j * r = r * j := fun j hj r hr =>
      (hcen r hr j (InternalSec.autOn_le_autOn_of_le hlt.le hj)).symm
    have hKYK := le_of_le_sup_of_perfect hperfA hJR IsNilpotent.to_isSolvable hsup
    intro k hk
    have hx : conjAct U ⟨k, hKYN hk⟩ ∈ KYs := Setup.mem_autOn_iff.2 ⟨_, hk, rfl⟩
    obtain ⟨g, hgK, hg⟩ := Setup.mem_autOn_iff.1 (hKYK hx)
    have h1 : conjAct U (g⁻¹ * ⟨k, hKYN hk⟩) = 1 := by
      rw [map_mul, map_inv, hg, inv_mul_cancel]
    have h2 : (g : G)⁻¹ * k ∈ Subgroup.centralizer (U : Set G) := A4.conjAct_eq_one_iff.mp h1
    have e : k = (g : G) * ((g : G)⁻¹ * k) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hgK
      ⟨KY.mul_mem (KY.inv_mem (hlt.le hgK)) hk, h2⟩
  ·
    have hp11 := A7.eleven_le_of_sq_mod_five hp hp5
    have hkn : σ.ker ≠ ⊤ := by
      intro h
      obtain ⟨k, hk⟩ := hσne
      exact hk ((MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top k))
    have hkZ : σ.ker ≤ Subgroup.center _ :=
      (CFSG.LocalCores.quasisimple_normal_subgroups hOq inferInstance).resolve_left hkn
    have hZ := A313.IsSL2.card_center hp (by omega) hpSL
    have hkc : Nat.card σ.ker ∣ 2 := by
      have := Subgroup.card_dvd_of_le hkZ
      rwa [hZ] at this
    have hcard := A313.IsSL2.card_eq hp hpSL
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup σ.ker
    rw [hcard, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective σ hσs).toEquiv] at h1
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup R'
    rw [hR'card] at h2
    have hpQ : p ∣ Nat.card Q := by
      have hpd : p ∣ Nat.card Q * Nat.card σ.ker := by rw [← h1]; exact Dvd.intro _ rfl
      rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
      · exact h
      · exact absurd (Nat.le_of_dvd (by norm_num) (h.trans hkc)) (by omega)
    obtain ⟨w, hw, hpw⟩ : ∃ w, Odd w ∧ p ^ 2 - 1 = 8 * w := by
      obtain ⟨j, hj⟩ : ∃ j, p = 8 * j + p % 8 := ⟨p / 8, (Nat.div_add_mod p 8).symm⟩
      rcases hp8 with h | h <;> rw [h] at hj <;> subst hj
      · exact ⟨8 * j ^ 2 + 6 * j + 1, ⟨4 * j ^ 2 + 3 * j, by ring⟩, by
          rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
          ring⟩
      · exact ⟨8 * j ^ 2 + 10 * j + 3, ⟨4 * j ^ 2 + 5 * j + 1, by ring⟩, by
          rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
          ring⟩
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    have hQ16 : ¬ 16 ∣ Nat.card Q := by
      intro h16
      have h3 : 16 ∣ p * (p ^ 2 - 1) := by
        rw [h1]
        exact Dvd.dvd.mul_right h16 _
      rw [hpw] at h3
      obtain ⟨a, rfl⟩ := hpodd
      obtain ⟨b, rfl⟩ := hw
      have h4 : 16 ∣ 8 * ((2 * a + 1) * (2 * b + 1)) := by
        have e : (2 * a + 1) * (8 * (2 * b + 1)) = 8 * ((2 * a + 1) * (2 * b + 1)) := by ring
        rw [← e]
        exact h3
      obtain ⟨c, hc⟩ := (odd_two_mul_add_one a).mul (odd_two_mul_add_one b)
      rw [hc] at h4
      omega
    have hKY16 : ¬ 16 ∣ Nat.card ↥KYs := by
      intro h16
      rw [h2] at h16
      have hcop : Nat.Coprime 16 (Nat.card ↥Rs) := by
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
        exact Nat.Coprime.pow_left 4 (Nat.coprime_two_left.mpr hRodd)
      exact hQ16 (hcop.dvd_of_dvd_mul_right h16)
    exact false_of_b56_prime hlist hqA h60 hKY16 hp hp11
      (h2 ▸ Dvd.dvd.mul_right hpQ _)

end CFSG.Quasithin.H13.Ch9.KGFF
