module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332T3
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFacts
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Tools
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Foundations.QuasisimpleMulEquiv
public import CFSG.Quasithin.Background.A3ComponentsQuotient
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.Foundations.KCoreOpen
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Open
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.LocalAnalysis.RankThreeTheoremC (KFactCentralOmega)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem inf_eq_bot_of_kFactCentralOmega (hCO : KFactCentralOmega) {K A₀ : Subgroup G}
    (hKq : CFSG.Open.IsQuasisimple ↥K) (hKK : CFSG.Open.IsKGroup ↥K)
    (hA₀card : Nat.card A₀ = 3) (hA₀C : A₀ ≤ centralizer (K : Set G))
    (hΩ : ∀ Q : Subgroup G, IsPGroup 3 Q → ∀ x ∈ Q, x ^ 3 = 1 → ∀ y ∈ Q, y ^ 3 = 1 →
      x * y = y * x)
    (hrk : ∀ X : Subgroup G, IsElemAbelian 3 X → Nat.card X ≤ 27) : A₀ ⊓ K = ⊥ := by
  classical
  by_contra hne
  have hA₀K : A₀ ≤ K := by
    have hdvd : Nat.card ↥(A₀ ⊓ K) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : A₀ ⊓ K ≤ A₀)
      rwa [hA₀card] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (Subgroup.card_eq_one.mp h1) hne
    · have heq : A₀ ⊓ K = A₀ :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hA₀card])
      exact heq.symm.le.trans inf_le_right
  have hZ : 3 ∣ Nat.card (Subgroup.center ↥K) := by
    have hle : A₀.subgroupOf K ≤ Subgroup.center ↥K := by
      intro a ha
      rw [Subgroup.mem_subgroupOf] at ha
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (hA₀C ha) k k.2)
    have hcard : Nat.card (A₀.subgroupOf K) = 3 := by
      rw [← hA₀card]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀K).toEquiv
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hle
  have hcat : CFSG.Open.IsCatalogGroup (↥K ⧸ Subgroup.center ↥K) :=
    @CFSG.Open.IsKGroup.isCatalogGroup_of_surjective (↥K ⧸ Subgroup.center ↥K) _
      (CFSG.Open.IsKGroup.quotient hKK (Subgroup.center ↥K))
      (⊤ : Subgroup (↥K ⧸ Subgroup.center ↥K)) (↥K ⧸ Subgroup.center ↥K) _ hKq.2
      (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥K hKq)
      (Subgroup.topEquiv (G := ↥K ⧸ Subgroup.center ↥K)).toMonoidHom
      (Subgroup.topEquiv (G := ↥K ⧸ Subgroup.center ↥K)).surjective
  have hrk' : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) < 4 := by
    have hle : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 3 := by
      refine CFSG.SectionRank.pRank_le (by norm_num) fun X _ hX => ?_
      have h1 := hrk (X.map K.subtype) (CFSG.SectionRank.isElemAbelian_map hX K.subtype)
      rw [Subgroup.card_map_of_injective K.subtype_injective] at h1
      simpa using h1
    omega
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 ↥K))
  apply hCO ↥K hKq hcat hZ hrk' S
  intro a ha b hb ha3 hb3
  have hQ : IsPGroup 3 ((S : Subgroup ↥K).map K.subtype) := S.isPGroup'.map K.subtype
  have hab := hΩ _ hQ (a : G) ⟨a, ha, rfl⟩ (by simpa using congrArg Subtype.val ha3)
    (b : G) ⟨b, hb, rfl⟩ (by simpa using congrArg Subtype.val hb3)
  exact Subtype.ext (by simpa using hab)

theorem exists_eq_sup_zpowers_of_card_nine {K E A₀ : Subgroup G} (hEel : IsElemAbelian 3 E)
    (hEcard : Nat.card E = 9)
    (hA₀E : A₀ ≤ E) (hA₀card : Nat.card A₀ = 3) (hA₀K : A₀ ⊓ K = ⊥) :
    ∃ e ∈ E, orderOf e = 3 ∧ E = A₀ ⊔ Subgroup.zpowers e ∧
      (E ⊓ K = Subgroup.zpowers e ∨ E ⊓ K = ⊥) := by
  classical
  have key : ∀ e ∈ E, e ∉ A₀ → orderOf e = 3 ∧ E = A₀ ⊔ Subgroup.zpowers e := by
    intro e heE heA
    have he1 : e ≠ 1 := fun h => heA (h ▸ A₀.one_mem)
    have hord : orderOf e = 3 := orderOf_eq_prime (hEel.2 e heE) he1
    have hecard : Nat.card (Subgroup.zpowers e) = 3 := by rw [Nat.card_zpowers, hord]
    have hinf : A₀ ⊓ Subgroup.zpowers e = ⊥ := by
      by_contra hne
      have hcarddvd : Nat.card ↥(A₀ ⊓ Subgroup.zpowers e) ∣ 3 := by
        have := Subgroup.card_dvd_of_le (inf_le_left : A₀ ⊓ Subgroup.zpowers e ≤ A₀)
        rwa [hA₀card] at this
      rcases (Nat.dvd_prime Nat.prime_three).mp hcarddvd with h1 | h3
      · exact hne (Subgroup.card_eq_one.mp h1)
      · have hinf_zpow : A₀ ⊓ Subgroup.zpowers e = Subgroup.zpowers e :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hecard])
        have hzpow_le : Subgroup.zpowers e ≤ A₀ := by
          rw [← hinf_zpow]
          exact inf_le_left
        exact heA (hzpow_le (Subgroup.mem_zpowers e))
    have hcomm : ∀ x ∈ A₀, ∀ y ∈ Subgroup.zpowers e, x * y = y * x := by
      intro x hx y hy
      have hxE : x ∈ E := hA₀E hx
      have hyE : y ∈ E := Subgroup.zpowers_le.mpr heE hy
      exact congrArg Subtype.val (hEel.1.is_comm.comm (⟨x, hxE⟩ : ↥E) (⟨y, hyE⟩ : ↥E))
    have hcardsup : Nat.card ↥(A₀ ⊔ Subgroup.zpowers e) = 9 := by
      have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A₀
        (Subgroup.zpowers e) hcomm).1
      rw [hinf, Subgroup.card_bot, mul_one, hA₀card, hecard] at hprod
      exact hprod
    have hsupE : A₀ ⊔ Subgroup.zpowers e ≤ E := sup_le hA₀E (Subgroup.zpowers_le.mpr heE)
    exact ⟨hord, (Subgroup.eq_of_le_of_card_ge hsupE (by rw [hcardsup, hEcard])).symm⟩
  by_cases hEK : E ⊓ K = ⊥
  · obtain ⟨e, heE, heA⟩ : ∃ e ∈ E, e ∉ A₀ := by
      by_contra hno
      push_neg at hno
      have := Subgroup.card_le_of_le (show E ≤ A₀ from hno)
      rw [hEcard, hA₀card] at this
      omega
    obtain ⟨hord, hEeq⟩ := key e heE heA
    exact ⟨e, heE, hord, hEeq, Or.inr hEK⟩
  · obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hEK
    have heE : (x : G) ∈ E := (Subgroup.mem_inf.mp x.2).1
    have heK : (x : G) ∈ K := (Subgroup.mem_inf.mp x.2).2
    have he1 : (x : G) ≠ 1 := fun h => hx (Subtype.ext h)
    have heA : (x : G) ∉ A₀ := by
      intro h
      have hmem : (x : G) ∈ A₀ ⊓ K := Subgroup.mem_inf.mpr ⟨h, heK⟩
      rw [hA₀K] at hmem
      exact he1 (Subgroup.mem_bot.mp hmem)
    obtain ⟨hord, hEeq⟩ := key x heE heA
    refine ⟨x, heE, hord, hEeq, Or.inl ?_⟩
    have hle : Subgroup.zpowers (x : G) ≤ E ⊓ K := Subgroup.zpowers_le.mpr x.2
    have hcardEK : Nat.card ↥(E ⊓ K) ≤ 3 := by
      have hdvd : Nat.card ↥(E ⊓ K) ∣ 3 ^ 2 := by
        have := Subgroup.card_dvd_of_le (inf_le_left : E ⊓ K ≤ E)
        rw [hEcard] at this
        norm_num
        exact this
      obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      interval_cases i
      · rw [hieq]; norm_num
      · rw [hieq]; norm_num
      · exfalso
        have heq : E ⊓ K = E :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hieq, hEcard]; norm_num)
        have hA₀bot : A₀ = ⊥ := by
          rw [← hA₀K]
          exact le_antisymm (le_inf le_rfl (hA₀E.trans (heq.symm.le.trans inf_le_right)))
            inf_le_left
        rw [hA₀bot, Subgroup.card_bot] at hA₀card
        omega
    exact (Subgroup.eq_of_le_of_card_ge hle
      (by rw [Nat.card_zpowers, hord]; exact hcardEK)).symm

theorem exists_elt_of_k332 (h332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    {K E A₀ : Subgroup G} (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hKE : CFSG.Open.IsKGroup ↥(K ⊔ E)) (hEN : E ≤ normalizer (K : Set G))
    (hEel : IsElemAbelian 3 E) (hEcard : Nat.card E = 9) (hA₀E : A₀ ≤ E)
    (hA₀card : Nat.card A₀ = 3) (hA₀C : A₀ ≤ centralizer (K : Set G)) (hA₀K : A₀ ⊓ K = ⊥)
    (hEK : ¬ E ≤ centralizer (K : Set G))
    (hΩ : ∀ Q : Subgroup G, IsPGroup 3 Q → ∀ x ∈ Q, x ^ 3 = 1 → ∀ y ∈ Q, y ^ 3 = 1 →
      x * y = y * x)
    (hrk : ∀ X : Subgroup G, IsElemAbelian 3 X → Nat.card X ≤ 27)
    (hwc : ∀ g ∈ K ⊔ E, E.map (MulAut.conj g).toMonoidHom ≤ centralizer (E : Set G) →
      E.map (MulAut.conj g).toMonoidHom = E) :
    ∃ e ∈ E, orderOf e = 3 ∧ E = A₀ ⊔ Subgroup.zpowers e ∧ (e ∈ K ∨ ¬ 3 ∣ Nat.card K) ∧
      CFSG.Open.pRank 3 K ≤ 1 := by
  classical
  obtain ⟨e, heE, he3, hEeq, hcase⟩ :=
    exists_eq_sup_zpowers_of_card_nine hEel hEcard hA₀E hA₀card hA₀K
  have he3' : e ^ 3 = 1 := hEel.2 e heE
  set T : Subgroup G := K ⊔ E with hTdef
  have hKT : K ≤ T := le_sup_left
  have hET : E ≤ T := le_sup_right
  have heT : e ∈ T := hET heE
  have hTNK : T ≤ normalizer (K : Set G) := sup_le Subgroup.le_normalizer hEN
  have hcentA : ∀ a ∈ A₀, ∀ k ∈ T, k * a * k⁻¹ = a := by
    intro a ha k hk
    have hTa : T ≤ centralizer ({a} : Set G) := by
      refine sup_le ?_ ?_
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact (Subgroup.mem_centralizer_iff.mp (hA₀C ha) x hx).symm
      · intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact congrArg Subtype.val (hEel.1.is_comm.comm ⟨a, hA₀E ha⟩ ⟨x, hx⟩)
    have hak := Subgroup.mem_centralizer_iff.mp (hTa hk) a (Set.mem_singleton a)
    calc k * a * k⁻¹ = a * k * k⁻¹ := by rw [hak]
      _ = a := by group
  have hwcZ : ∀ S : Subgroup G, IsPGroup 3 S → E ≤ S → ∀ k ∈ T, k * e * k⁻¹ ∈ S →
      k * e * k⁻¹ ∈ Subgroup.zpowers e := by
    intro S hS hES k hk hkS
    have hEk : E.map (MulAut.conj k).toMonoidHom ≤ centralizer (E : Set G) := by
      have hmapE : E.map (MulAut.conj k).toMonoidHom =
          A₀.map (MulAut.conj k).toMonoidHom ⊔ Subgroup.zpowers (k * e * k⁻¹) := by
        calc E.map (MulAut.conj k).toMonoidHom
            = (A₀ ⊔ Subgroup.zpowers e).map (MulAut.conj k).toMonoidHom := by rw [← hEeq]
          _ = _ := by
            rw [Subgroup.map_sup, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
              MulAut.conj_apply]
      rw [hmapE]
      refine sup_le ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        change k * a * k⁻¹ ∈ centralizer (E : Set G)
        rw [hcentA a ha k hk, Subgroup.mem_centralizer_iff]
        intro y hy
        exact congrArg Subtype.val (hEel.1.is_comm.comm ⟨y, hy⟩ ⟨a, hA₀E ha⟩)
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro y hy
        have hke3 : (k * e * k⁻¹) ^ 3 = 1 := by
          rw [conj_pow, he3', mul_one, mul_inv_cancel]
        exact hΩ S hS y (hES hy) (hEel.2 y hy) (k * e * k⁻¹) hkS hke3
    have hEkeq := hwc k hk hEk
    have hkeE : k * e * k⁻¹ ∈ E := by
      rw [← hEkeq]
      exact ⟨e, heE, rfl⟩
    rcases hcase with hEKe | hEKbot
    · have heK : e ∈ K := by
        have hmem : e ∈ E ⊓ K := by
          rw [hEKe]
          exact Subgroup.mem_zpowers e
        exact (Subgroup.mem_inf.mp hmem).2
      have hkeK : k * e * k⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hTNK hk) e).mp heK
      rw [← hEKe]
      exact Subgroup.mem_inf.mpr ⟨hkeE, hkeK⟩
    · have hk' : k ∈ ((K : Set G) * (E : Set G)) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left K E hEN]
        exact hk
      obtain ⟨c, hc, f, hf, rfl⟩ := Set.mem_mul.mp hk'
      have hfe : f * e = e * f :=
        congrArg Subtype.val (hEel.1.is_comm.comm ⟨f, hf⟩ ⟨e, heE⟩)
      have hkce : c * f * e * (c * f)⁻¹ = c * e * c⁻¹ := by
        calc c * f * e * (c * f)⁻¹ = c * (f * e) * f⁻¹ * c⁻¹ := by group
          _ = c * (e * f) * f⁻¹ * c⁻¹ := by rw [hfe]
          _ = c * e * c⁻¹ := by group
      rw [hkce] at hkeE ⊢
      have hwK : c * e * c⁻¹ * e⁻¹ ∈ K := by
        have h1 : e * c⁻¹ * e⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (hEN heE) c⁻¹).mp (K.inv_mem hc)
        have h2 := K.mul_mem hc h1
        simpa [mul_assoc] using h2
      have hwE : c * e * c⁻¹ * e⁻¹ ∈ E := E.mul_mem hkeE (E.inv_mem heE)
      have hw1 : c * e * c⁻¹ * e⁻¹ = 1 := by
        have hmem : c * e * c⁻¹ * e⁻¹ ∈ E ⊓ K := Subgroup.mem_inf.mpr ⟨hwE, hwK⟩
        rw [hEKbot] at hmem
        exact Subgroup.mem_bot.mp hmem
      have hce : c * e * c⁻¹ = e := by
        calc c * e * c⁻¹ = c * e * c⁻¹ * e⁻¹ * e := by group
          _ = e := by rw [hw1, one_mul]
      rw [hce]
      exact Subgroup.mem_zpowers e
  let e' : ↥T := ⟨e, heT⟩
  have hE'p : IsPGroup 3 (E.subgroupOf T) :=
    (CFSG.Open.IsElemAbelian.isPGroup hEel).comap_subtype
  obtain ⟨P, hE'P⟩ := hE'p.exists_le_sylow
  set S : Subgroup G := (P : Subgroup ↥T).map T.subtype with hSdef
  have hSp : IsPGroup 3 S := P.isPGroup'.map T.subtype
  have hES : E ≤ S := fun x hx =>
    ⟨⟨x, hET hx⟩, hE'P (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf 3 S T := ⟨P, rfl⟩
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 (P : Subgroup ↥T) ⊤ :=
    (CFSG.ABGLocalTools.isSylowOf_iff (p := 3)).2 ⟨le_top, P.isPGroup', by
      rw [Subgroup.relIndex_top_right]
      exact P.not_dvd_index⟩
  have hΩP : ∀ x ∈ (P : Subgroup ↥T), x ^ 3 = 1 → ∀ y ∈ (P : Subgroup ↥T), y ^ 3 = 1 →
      x * y = y * x := by
    intro x hx hx3 y hy hy3
    apply Subtype.ext
    exact hΩ S hSp (x : G) ⟨x, hx, rfl⟩ (by simpa using congrArg Subtype.val hx3)
      (y : G) ⟨y, hy, rfl⟩ (by simpa using congrArg Subtype.val hy3)
  have hrkP : CFSG.Open.pRank 3 (P : Subgroup ↥T) ≤ 3 := by
    refine CFSG.SectionRank.pRank_le (by norm_num) fun X _ hX => ?_
    have h1 := hrk (X.map T.subtype) (CFSG.SectionRank.isElemAbelian_map hX T.subtype)
    rw [Subgroup.card_map_of_injective T.subtype_injective] at h1
    simpa using h1
  have hZP : Subgroup.zpowers e' ≤ (P : Subgroup ↥T) :=
    Subgroup.zpowers_le.mpr (hE'P (Subgroup.mem_subgroupOf.mpr heE))
  have hZcard : Nat.card (Subgroup.zpowers e') = 3 := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe e']
    exact he3
  have hwcT : IsWeaklyClosedIn (Subgroup.zpowers e') (P : Subgroup ↥T) := by
    intro g hg
    have hle : (Subgroup.zpowers e').map (MulAut.conj g⁻¹).toMonoidHom ≤
        Subgroup.zpowers e' := by
      rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
      have hmemP : (MulAut.conj g⁻¹).toMonoidHom e' ∈ (P : Subgroup ↥T) := by
        apply hg
        exact ⟨e', Subgroup.mem_zpowers e', rfl⟩
      have hmemS : ((g⁻¹ : ↥T) : G) * e * ((g⁻¹ : ↥T) : G)⁻¹ ∈ S := ⟨_, hmemP, rfl⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hwcZ S hSp hES _ (g⁻¹).2 hmemS)
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext ?_⟩
      simpa [MulAut.conj_apply] using hn
    show (Subgroup.zpowers e').map (MulAut.conj g⁻¹).toMonoidHom = Subgroup.zpowers e'
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective])
  have hNC := h332 ↥T hKE (P : Subgroup ↥T) hPsyl hΩP hrkP (Subgroup.zpowers e') hZP hZcard
    hwcT
  set N : Subgroup ↥T :=
    Subgroup.normalClosure ((Subgroup.zpowers e' : Subgroup ↥T) : Set ↥T) with hNdef
  set NG : Subgroup G := N.map T.subtype with hNGdef
  have hNGT : NG ≤ T := Subgroup.map_subtype_le N
  have hmemNG : ∀ x : ↥T, x ∈ N → (x : G) ∈ NG := fun x hx => ⟨x, hx, rfl⟩
  have hsubN : ∀ X : Subgroup G, X ≤ NG → X.subgroupOf T ≤ N := by
    intro X hXN x hx
    obtain ⟨n, hn, hnx⟩ := hXN (Subgroup.mem_subgroupOf.mp hx)
    have hnx' : n = x := Subtype.ext hnx
    rw [← hnx']
    exact hn
  have hbound : ∀ X : Subgroup G, X ≤ NG → IsElemAbelian 3 X → Nat.card X ≤ 3 := by
    intro X hXN hX
    have hXT : X ≤ T := hXN.trans hNGT
    have hX'el : IsElemAbelian 3 (X.subgroupOf T) := hX.subgroupOf T
    have hcardX' : Nat.card (X.subgroupOf T) = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXT).toEquiv
    have h1 := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hX'el
    have h2 := CFSG.SectionRank.le_pRank (by norm_num) (hsubN X hXN) hX'el h1
    rw [hNC] at h2
    rw [← hcardX', h1]
    calc 3 ^ CFSG.Open.pRank 3 (X.subgroupOf T) ≤ 3 ^ 1 :=
          Nat.pow_le_pow_right (by norm_num) h2
      _ = 3 := by norm_num
  have hK'n : (K.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKT).mpr hTNK
  have hK'q : CFSG.Open.IsQuasisimple ↥(K.subgroupOf T) :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp
      ((CFSG.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hKT)).mpr
        (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hKq))
  have heC : e ∉ centralizer (K : Set G) := by
    intro hc
    apply hEK
    rw [hEeq]
    exact sup_le hA₀C (Subgroup.zpowers_le.mpr hc)
  have hZK' : ⁅Subgroup.zpowers e', K.subgroupOf T⁆ = K.subgroupOf T := by
    refine CFSG.LocalAnalysis.GLTheoremB.commutator_eq_of_isQuasisimple hK'q ?_ ?_
    · intro x _
      refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => hK'n.conj_mem h hh x,
        fun hh => ?_⟩
      have h2 := hK'n.conj_mem _ hh x⁻¹
      simpa [mul_assoc] using h2
    · intro hle
      apply heC
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hmem := hle (Subgroup.mem_zpowers e')
      rw [Subgroup.mem_centralizer_iff] at hmem
      exact congrArg Subtype.val (hmem ⟨k, hKT hk⟩ (Subgroup.mem_subgroupOf.mpr hk))
  have hK'N : K.subgroupOf T ≤ N := by
    calc K.subgroupOf T = ⁅Subgroup.zpowers e', K.subgroupOf T⁆ := hZK'.symm
      _ ≤ ⁅N, K.subgroupOf T⁆ := Subgroup.commutator_mono Subgroup.le_normalClosure le_rfl
      _ ≤ N := Subgroup.commutator_le_left N _
  have hKNG : K ≤ NG := fun k hk =>
    hmemNG ⟨k, hKT hk⟩ (hK'N (Subgroup.mem_subgroupOf.mpr hk))
  have heNG : e ∈ NG := hmemNG e' (Subgroup.le_normalClosure (Subgroup.mem_zpowers e'))
  have hrkK : CFSG.Open.pRank 3 K ≤ 1 := by
    refine CFSG.SectionRank.pRank_le (by norm_num) fun X hXK hX => ?_
    simpa using hbound X (hXK.trans hKNG) hX
  have hcase' : e ∈ K ∨ ¬ 3 ∣ Nat.card K := by
    rcases hcase with hEKe | hEKbot
    · left
      have hmem : e ∈ E ⊓ K := by
        rw [hEKe]
        exact Subgroup.mem_zpowers e
      exact (Subgroup.mem_inf.mp hmem).2
    · right
      intro h3K
      have hSK : CFSG.ABGLocalTools.IsSylowOf 3 (S ⊓ K) K :=
        hSsyl.inf_of_le_normalizer hKT hTNK
      have hSKne : S ⊓ K ≠ ⊥ := by
        intro hbot
        have hc := hSK.card_eq
        rw [hbot, Subgroup.card_bot] at hc
        have hpos : 0 < (Nat.card K).factorization 3 :=
          Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' h3K
        have h3le : 3 ≤ 3 ^ (Nat.card K).factorization 3 := Nat.le_self_pow hpos.ne' 3
        omega
      have hHn : ((S ⊓ K).subgroupOf S).Normal := by
        refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr ?_
        intro s hs
        have hsT : s ∈ T := hSsyl.le hs
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          obtain ⟨hxS, hxK⟩ := Subgroup.mem_inf.mp hx
          exact Subgroup.mem_inf.mpr ⟨S.mul_mem (S.mul_mem hs hxS) (S.inv_mem hs),
            (Subgroup.mem_normalizer_iff.mp (hTNK hsT) x).mp hxK⟩
        · intro hx
          obtain ⟨hxS, hxK⟩ := Subgroup.mem_inf.mp hx
          refine Subgroup.mem_inf.mpr ⟨?_, (Subgroup.mem_normalizer_iff.mp (hTNK hsT) x).mpr hxK⟩
          have h2 := S.mul_mem (S.mul_mem (S.inv_mem hs) hxS) hs
          simpa [mul_assoc] using h2
      have hHne : (S ⊓ K).subgroupOf S ≠ ⊥ := by
        intro hbot
        apply hSKne
        rw [eq_bot_iff]
        intro x hx
        have hmem : (⟨x, (Subgroup.mem_inf.mp hx).1⟩ : ↥S) ∈ (S ⊓ K).subgroupOf S :=
          Subgroup.mem_subgroupOf.mpr hx
        rw [hbot] at hmem
        exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hmem))
      have hW := @Group.IsNilpotent.inf_center_ne_bot_of_normal ↥S _ hSp.isNilpotent
        ((S ⊓ K).subgroupOf S) hHn hHne
      set W : Subgroup ↥S := (S ⊓ K).subgroupOf S ⊓ Subgroup.center ↥S with hWdef
      have hWp : IsPGroup 3 W := hSp.to_subgroup W
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hWp
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hm
        exact hW (Subgroup.card_eq_one.mp hm)
      have h3W : 3 ∣ Nat.card W := by
        rw [hm]
        exact dvd_pow_self 3 hm0
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥W) 3 h3W
      have hyW : (y : ↥S) ∈ W := y.2
      have hyK : ((y : ↥S) : G) ∈ K :=
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hyW).1)).2
      have hey : e * ((y : ↥S) : G) = ((y : ↥S) : G) * e := by
        have hcen := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp hyW).2 ⟨e, hES heE⟩
        exact congrArg Subtype.val hcen
      have hordy : orderOf ((y : ↥S) : G) = 3 :=
        (Subgroup.orderOf_coe _).trans ((Subgroup.orderOf_coe y).trans hy)
      have hy3 : ((y : ↥S) : G) ^ 3 = 1 := by
        rw [← hordy]
        exact pow_orderOf_eq_one _
      have hcommX : ∀ a ∈ Subgroup.zpowers e, ∀ b ∈ Subgroup.zpowers ((y : ↥S) : G),
          a * b = b * a := by
        intro a ha b hb
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact (Commute.zpow_zpow (show Commute e ((y : ↥S) : G) from hey) i j).eq
      have hXel : IsElemAbelian 3 (Subgroup.zpowers e ⊔ Subgroup.zpowers ((y : ↥S) : G)) :=
        (CFSG.Open.isElemAbelian_zpowers he3').sup_of_commute
          (CFSG.Open.isElemAbelian_zpowers hy3) hcommX
      have hinfX : Subgroup.zpowers e ⊓ Subgroup.zpowers ((y : ↥S) : G) = ⊥ := by
        rw [eq_bot_iff, ← hEKbot]
        exact inf_le_inf (Subgroup.zpowers_le.mpr heE) (Subgroup.zpowers_le.mpr hyK)
      have hXcard : Nat.card ↥(Subgroup.zpowers e ⊔ Subgroup.zpowers ((y : ↥S) : G)) = 9 := by
        have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers e)
          (Subgroup.zpowers ((y : ↥S) : G)) hcommX).1
        rw [hinfX, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, he3,
          hordy] at hc
        exact hc
      have hXNG : Subgroup.zpowers e ⊔ Subgroup.zpowers ((y : ↥S) : G) ≤ NG :=
        sup_le (Subgroup.zpowers_le.mpr heNG) (Subgroup.zpowers_le.mpr (hKNG hyK))
      have := hbound _ hXNG hXel
      omega
  exact ⟨e, heE, he3, hEeq, hcase', hrkK⟩

end CFSG.LocalAnalysis.UniquenessCase.UCK
