module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBL31B
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4
open scoped commutatorElement Pointwise

section Lemma323

variable {G : Type} [Group G] [Finite G]

private theorem mem_normalizer_commutator_nsb323 {X Y : Subgroup G} {g : G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((⁅X, Y⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hX hY ⊢
  rw [Subgroup.map_commutator, hX, hY]

private theorem mem_normalizer_centralizer_nsb323 {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    ∀ c ∈ Subgroup.centralizer (X : Set G), g * c * g⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' : g⁻¹ * v * g ∈ X := (Subgroup.mem_normalizer_iff''.mp hg v).mp hv
  have h1 := (Subgroup.mem_centralizer_iff.mp hc) _ hv'
  calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * v := by group

private theorem sup_le_normalizer_vV_nsb323 {T M L I H K : Subgroup G}
    (c : Conf4212 G T M L I H K) :
    L ⊔ T ≤ Subgroup.normalizer ((vV T L : Subgroup G) : Set G) := by
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := c.hyp421.T_le.trans c.normal
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    _root_.sup_le Subgroup.le_normalizer hTN
  have hRN : L ⊔ T ≤ Subgroup.normalizer (reducedAggregate (L ⊔ T) : Set G) := by
    rw [← c.omega_eq]
    exact (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_omegaOneCenterOf _)
  intro g hg
  exact mem_normalizer_commutator_nsb323 (hRN hg) (hLTN hg)

private theorem normalizer_vV_le_nsb323 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K) :
    Subgroup.normalizer ((vV T L : Subgroup G) : Set G) ≤ M := by
  have hV2 : IsPGroup 2 (vV T L) := by
    obtain ⟨-, hexp⟩ := c.hypC28.V_elem
    rintro ⟨x, hx⟩
    exact ⟨1, Subtype.ext (by simpa using hexp x hx)⟩
  have hpC : pCoreOf 2 (Subgroup.normalizer ((vV T L : Subgroup G) : Set G)) ≠ ⊥ := by
    intro hbot
    have h1 : vV T L ≤ pCoreOf 2 (Subgroup.normalizer ((vV T L : Subgroup G) : Set G)) :=
      le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hV2
    rw [hbot] at h1
    exact c.hypC28.V_ne (le_bot_iff.mp h1)
  exact isUniqueM_le_of_inH (c.hyp421.isUniqueM_sup h37 h38 h39).1
    ⟨sup_le_normalizer_vV_nsb323 c, hpC⟩

private theorem mem_centralizerSection_nsb323 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) {T M L Mm I H K : Subgroup G} {m k : ℕ}
    (hd : NoSumBigData G T M L Mm I H K m k) {z : G}
    (hzN : z ∈ Subgroup.normalizer ((vV T L : Subgroup G) : Set G))
    (hcomm : ∀ l ∈ L, ⁅z, l⁆ ∈ Subgroup.centralizer ((vV T L : Subgroup G) : Set G)) :
    z ∈ centralizerSection M L (pCoreOf 2 L) := by
  have hc : Conf4212 G T M L I H K := hd.2.2.1
  have hzM : z ∈ M := normalizer_vV_le_nsb323 h37 h38 h39 hc hzN
  have hzL : z ∈ Subgroup.normalizer (L : Set G) := hc.normal hzM
  refine mem_centralizerSection.mpr ⟨hzM, hzL, normalizer_le_normalizer_pCoreOf 2 L hzL, ?_⟩
  intro l hl
  have hmem : z * l * z⁻¹ * l⁻¹ ∈ L ⊓ Subgroup.centralizer ((vV T L : Subgroup G) : Set G) := by
    refine ⟨?_, hcomm l hl⟩
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp hzL l).mp hl) (L.inv_mem hl)
  rw [inf_centralizer_vV_eq hd] at hmem
  have e : l * z * l⁻¹ * z⁻¹ = (z * l * z⁻¹ * l⁻¹)⁻¹ := by group
  rw [e]
  exact (pCoreOf 2 L).inv_mem hmem

private theorem mem_of_pow_two_pow_nsb323 {D N : Subgroup G} (hND : N ≤ D)
    (hnorm : ∀ d ∈ D, ∀ n ∈ N, d * n * d⁻¹ ∈ N) (hodd : ¬ 2 ∣ N.relIndex D)
    {x : G} (hxD : x ∈ D) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x ∈ N := by
  haveI : (N.subgroupOf D).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g g.2 n hn⟩
  set q : ↥D ⧸ N.subgroupOf D := QuotientGroup.mk ⟨x, hxD⟩ with hq
  have hq1 : q ^ 2 ^ k = 1 := by
    have h1 : (⟨x, hxD⟩ : ↥D) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [hq, ← QuotientGroup.mk_pow, h1, QuotientGroup.mk_one]
  have h1 : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hq1
  have h2 : orderOf q ∣ N.relIndex D := orderOf_dvd_natCard q
  have hcop : Nat.Coprime (2 ^ k) (N.relIndex D) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  have h4 : orderOf q = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff, hq, QuotientGroup.eq_one_iff] at h4
  exact Subgroup.mem_subgroupOf.1 h4

private theorem mem_centralizer_of_two_elt_nsb323 {C Nv W R : Subgroup G}
    (hRC : R ≤ C) (hRW : R ≤ W) (hWN : W ≤ Nv)
    (hNW : ∀ d ∈ Nv, ∀ w ∈ W, d * w * d⁻¹ ∈ W) (hodd : ¬ 2 ∣ R.relIndex C)
    {x : G} (hxC : x ∈ C) (hxN : x ∈ Nv) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x ∈ W := by
  have hRD : R ≤ C ⊓ Nv := le_inf hRC (hRW.trans hWN)
  have hRN : R ≤ (C ⊓ Nv) ⊓ W := le_inf hRD hRW
  have hnorm : ∀ d ∈ C ⊓ Nv, ∀ n ∈ (C ⊓ Nv) ⊓ W, d * n * d⁻¹ ∈ (C ⊓ Nv) ⊓ W := by
    intro d hd n hn
    exact ⟨⟨C.mul_mem (C.mul_mem hd.1 hn.1.1) (C.inv_mem hd.1),
      Nv.mul_mem (Nv.mul_mem hd.2 hn.1.2) (Nv.inv_mem hd.2)⟩, hNW d hd.2 n hn.2⟩
  have hodd' : ¬ 2 ∣ ((C ⊓ Nv) ⊓ W).relIndex (C ⊓ Nv) := by
    have h1 : R.relIndex (C ⊓ Nv) * (C ⊓ Nv).relIndex C = R.relIndex C :=
      Subgroup.relIndex_mul_relIndex R (C ⊓ Nv) C hRD inf_le_left
    have h2 : R.relIndex ((C ⊓ Nv) ⊓ W) * ((C ⊓ Nv) ⊓ W).relIndex (C ⊓ Nv) =
        R.relIndex (C ⊓ Nv) :=
      Subgroup.relIndex_mul_relIndex R ((C ⊓ Nv) ⊓ W) (C ⊓ Nv) hRN inf_le_left
    have hdvd : ((C ⊓ Nv) ⊓ W).relIndex (C ⊓ Nv) ∣ R.relIndex C :=
      ⟨R.relIndex ((C ⊓ Nv) ⊓ W) * (C ⊓ Nv).relIndex C, by rw [← h1, ← h2]; ring⟩
    exact fun h => hodd (h.trans hdvd)
  exact (mem_of_pow_two_pow_nsb323 inf_le_left hnorm hodd' ⟨hxC, hxN⟩ hk).2

end Lemma323

theorem lemma323'_holds (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    Lemma323' := by
  intro G _ _ T M L Mm I H K m k hd z hzN hcomm
  have hc : Conf4212 G T M L I H K := hd.2.2.1
  have hzC : z ∈ centralizerSection M L (pCoreOf 2 L) :=
    mem_centralizerSection_nsb323 h37 h38 h39 hd hzN hcomm
  have hRT : pCoreOf 2 (L ⊔ T) = T ⊓ centralizerSection M L (pCoreOf 2 L) :=
    hc.hyp421.pCoreOf_sup_eq hc.normal
  have hRC : pCoreOf 2 (L ⊔ T) ≤ centralizerSection M L (pCoreOf 2 L) := by
    rw [hRT]
    exact inf_le_right
  have hRW : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer ((vV T L : Subgroup G) : Set G) :=
    hc.pCoreOf_le_centralizer_V le_rfl
  have hodd : ¬ 2 ∣ (pCoreOf 2 (L ⊔ T)).relIndex (centralizerSection M L (pCoreOf 2 L)) := by
    have hT : IsSylowTwoOf T M :=
      CFSG.Quasithin.H13.Ch4.isSylowTwoOf_of_le hc.hyp421.sylow hc.hyp421.T_le
    have hCM : M ≤ Subgroup.normalizer
        ((centralizerSection M L (pCoreOf 2 L) : Subgroup G) : Set G) :=
      centralizerSection_normal hc.normal
    have hsyl := CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hT
      (centralizerSection_le_left M L _) hCM
    rw [hRT]
    exact hsyl.2.2
  obtain ⟨a, e, he, hoe⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  have hpow : (z ^ e) ^ 2 ^ a = 1 := by
    rw [← pow_mul]
    have hea : e * 2 ^ a = orderOf z := by rw [hoe]; ring
    rw [hea, pow_orderOf_eq_one]
  refine ⟨e, he, ?_⟩
  exact mem_centralizer_of_two_elt_nsb323 hRC hRW (Subgroup.centralizer_le_normalizer _)
    (fun d hd w hw => mem_normalizer_centralizer_nsb323 hd w hw) hodd
    ((centralizerSection M L (pCoreOf 2 L)).pow_mem hzC e) (Subgroup.pow_mem _ hzN e) hpow

end CFSG.Quasithin.H13.Ch4.NSB
