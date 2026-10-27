module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Pure
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma18
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Walter.PSL2Facts.Even
public import Certificates.Data.A5
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.BenderSuzuki.MatrixGroups (PSL2MatrixGroup)

theorem two_le_pRank_psl2_three_pow {K : Type} [Group K] [Finite K] {f : ℕ}
    (hK : LieModel K .PSL 2 3 f) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hadm, F, hFld, hFin, hFcard, ⟨eK⟩⟩ := hK.statedClassicalModel (by decide)
  haveI : Fintype F := Fintype.ofFinite F
  have hf1 : 1 ≤ f := hadm.2.1
  have hf2 : 2 ≤ f := by
    have hne : 3 ^ f ≠ 3 := fun h => hadm.2.2.2.2 (by rw [h])
    have hne1 : f ≠ 1 := fun h1 => hne (by norm_num [h1])
    omega
  have hchar : CharP F 3 := charP_of_card_eq_prime_pow (by simpa using hFcard)
  let φ : K ≃* PSL2MatrixGroup F := eK.trans (CFSG.GH74.GLS.IVK.L2.equivPSL F)
  let P : Sylow 3 (PSL2MatrixGroup F) := default
  obtain ⟨eQ⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hFcard P
  have hpow : ∀ x : Multiplicative F, x ^ 3 = 1 := by
    intro x
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  have hM : CFSG.Open.IsElemAbelian 3 (⊤ : Subgroup (Multiplicative F)) :=
    ⟨IsMulCommutative.of_comm fun a b => mul_comm a b, fun x _ => hpow x⟩
  have hQtop : CFSG.Open.IsElemAbelian 3 (⊤ : Subgroup ↥P) := by
    have h := CFSG.Open.IsElemAbelian.map hM eQ.toMonoidHom
    rwa [Subgroup.map_top_of_surjective _ eQ.surjective] at h
  have hPel : CFSG.Open.IsElemAbelian 3 (P : Subgroup (PSL2MatrixGroup F)) := by
    have h := CFSG.Open.IsElemAbelian.map hQtop (P : Subgroup (PSL2MatrixGroup F)).subtype
    rwa [show (⊤ : Subgroup ↥P).map (P : Subgroup (PSL2MatrixGroup F)).subtype =
      (P : Subgroup (PSL2MatrixGroup F)) from by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]] at h
  have hcardP : Nat.card (P : Subgroup (PSL2MatrixGroup F)) = 3 ^ f := by
    have h1 : Nat.card (P : Subgroup (PSL2MatrixGroup F)) = Nat.card (Multiplicative F) :=
      (Nat.card_congr eQ.toEquiv).symm
    rw [h1, Nat.card_congr Multiplicative.toAdd, hFcard]
  have hcardE : Nat.card (P.map φ.symm.toMonoidHom) = 3 ^ f := by
    rw [Subgroup.card_map_of_injective φ.symm.injective]
    simpa using hcardP
  exact le_trans hf2 (CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top
    (CFSG.Open.IsElemAbelian.map hPel φ.symm.toMonoidHom) hcardE)

private theorem r925_psl2_torus_align
    {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (P : Sylow p (PSL2MatrixGroup F))
    {U S U0 S0 : Subgroup (PSL2MatrixGroup F)}
    (hUcyclic : IsCyclic U)
    (hUcard : Nat.card U = (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2)
    (hScyclic : IsCyclic S)
    (hScard : Nat.card S = (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)
    (hpartition : ∀ x : PSL2MatrixGroup F, x ≠ 1 →
      ∃! T : Subgroup (PSL2MatrixGroup F), x ∈ T ∧
        ((∃ g, T = (P : Subgroup (PSL2MatrixGroup F)).map
            (MulAut.conj g).toMonoidHom) ∨
          (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
          (∃ g, T = S.map (MulAut.conj g).toMonoidHom)))
    (hU0cyclic : IsCyclic U0)
    (hU0card : Nat.card U0 = (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2)
    (hS0cyclic : IsCyclic S0)
    (hS0card : Nat.card S0 = (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2) :
    (∃ g, U0 = U.map (MulAut.conj g).toMonoidHom) ∧
      (∃ g, S0 = S.map (MulAut.conj g).toMonoidHom) := by
  classical
  have hPcard : Nat.card (P : Subgroup (PSL2MatrixGroup F)) = Nat.card F := by
    obtain ⟨eP⟩ := CFSG.BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hFcard P
    exact (Nat.card_congr eP.toEquiv).symm
  have hU0cardU : Nat.card U0 = Nat.card U := hU0card.trans hUcard.symm
  have hS0cardS : Nat.card S0 = Nat.card S := hS0card.trans hScard.symm
  constructor
  · by_cases hUbot : U = ⊥
    · have hbotU0 : (⊥ : Subgroup (PSL2MatrixGroup F)) = U0 := by
        apply Subgroup.eq_of_le_of_card_ge bot_le
        rw [hU0cardU, hUbot]
      refine ⟨1, ?_⟩
      rw [← hbotU0, hUbot]
      simp
    · have hU0ne : U0 ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hU0cardU]
        exact (Subgroup.one_lt_card_iff_ne_bot U).2 hUbot
      obtain ⟨u, hu_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU0ne
      have huG : (u : PSL2MatrixGroup F) ≠ 1 := by
        intro hu
        exact hu_ne (Subtype.ext hu)
      obtain ⟨T, huT, hTfamily⟩ := (hpartition (u : PSL2MatrixGroup F) huG).exists
      have hU0leT : U0 ≤ T :=
        CFSG.BenderSuzuki.lemma114_cyclic_le_unique_partition_family _ hpartition
          huG huT hTfamily u.property hU0cyclic
      rcases hTfamily with ⟨g, hTg⟩ | ⟨g, hTg⟩ | ⟨g, hTg⟩
      · exfalso
        have hcop : Nat.Coprime (Nat.card U0) (Nat.card T) := by
          rw [hTg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hPcard, hU0card]
          exact (CFSG.Glauberman.Dickson.hq_coprime_split_order (Nat.card F)
            Nat.card_pos).symm
        exact huG (CFSG.Glauberman.Dickson.hmem_eq_one_of_coprime_card U0 T hcop
          u.property (hU0leT u.property))
      · refine ⟨g, ?_⟩
        calc
          U0 = T := Subgroup.eq_of_le_of_card_ge hU0leT (by
            rw [hTg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hU0cardU])
          _ = U.map (MulAut.conj g).toMonoidHom := hTg
      · exfalso
        have hcop : Nat.Coprime (Nat.card U0) (Nat.card T) := by
          rw [hTg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hScard, hU0card]
          exact CFSG.BenderSuzuki.External.hsplit_nonsplit_order_coprime
            (Nat.card F) (Finite.one_lt_card (α := F))
        exact huG (CFSG.Glauberman.Dickson.hmem_eq_one_of_coprime_card U0 T hcop
          u.property (hU0leT u.property))
  · by_cases hSbot : S = ⊥
    · have hbotS0 : (⊥ : Subgroup (PSL2MatrixGroup F)) = S0 := by
        apply Subgroup.eq_of_le_of_card_ge bot_le
        rw [hS0cardS, hSbot]
      refine ⟨1, ?_⟩
      rw [← hbotS0, hSbot]
      simp
    · have hS0ne : S0 ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hS0cardS]
        exact (Subgroup.one_lt_card_iff_ne_bot S).2 hSbot
      obtain ⟨s0, hs0_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS0ne
      have hs0G : (s0 : PSL2MatrixGroup F) ≠ 1 := by
        intro hs0
        exact hs0_ne (Subtype.ext hs0)
      obtain ⟨T, hs0T, hTfamily⟩ := (hpartition (s0 : PSL2MatrixGroup F) hs0G).exists
      have hS0leT : S0 ≤ T :=
        CFSG.BenderSuzuki.lemma114_cyclic_le_unique_partition_family _ hpartition
          hs0G hs0T hTfamily s0.property hS0cyclic
      rcases hTfamily with ⟨g, hTg⟩ | ⟨g, hTg⟩ | ⟨g, hTg⟩
      · exfalso
        have hcop : Nat.Coprime (Nat.card S0) (Nat.card T) := by
          rw [hTg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hPcard, hS0card]
          exact (CFSG.Glauberman.Dickson.hq_coprime_nonsplit_order (Nat.card F)
            Nat.card_pos).symm
        exact hs0G (CFSG.Glauberman.Dickson.hmem_eq_one_of_coprime_card S0 T hcop
          s0.property (hS0leT s0.property))
      · exfalso
        have hcop : Nat.Coprime (Nat.card S0) (Nat.card T) := by
          rw [hTg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hUcard, hS0card]
          exact (CFSG.BenderSuzuki.External.hsplit_nonsplit_order_coprime
            (Nat.card F) (Finite.one_lt_card (α := F))).symm
        exact hs0G (CFSG.Glauberman.Dickson.hmem_eq_one_of_coprime_card S0 T hcop
          s0.property (hS0leT s0.property))
      · refine ⟨g, ?_⟩
        calc
          S0 = T := Subgroup.eq_of_le_of_card_ge hS0leT (by
            rw [hTg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hS0cardS])
          _ = S.map (MulAut.conj g).toMonoidHom := hTg

private theorem r925_reflection_transport {G : Type*} [Group G]
    (T : Subgroup G) (w : G) (hcyc : IsCyclic T)
    (hcard : Nat.card (T ⊔ Subgroup.zpowers w : Subgroup G) = 2 * Nat.card T)
    (hnorm : ∀ R : Subgroup G, R ≤ T → R ≠ ⊥ →
      Subgroup.normalizer (R : Set G) = T ⊔ Subgroup.zpowers w)
    (e : G ≃* G) :
    IsCyclic (T.map e.toMonoidHom) ∧
      Nat.card (T.map e.toMonoidHom ⊔ Subgroup.zpowers (e w) : Subgroup G) =
        2 * Nat.card (T.map e.toMonoidHom) ∧
      ∀ R : Subgroup G, R ≤ T.map e.toMonoidHom → R ≠ ⊥ →
        Subgroup.normalizer (R : Set G) = T.map e.toMonoidHom ⊔ Subgroup.zpowers (e w) := by
  haveI : IsCyclic T := hcyc
  refine ⟨isCyclic_of_surjective _ (e.toMonoidHom.subgroupMap_surjective T), ?_, ?_⟩
  · have hmap : (T.map e.toMonoidHom ⊔ Subgroup.zpowers (e w) : Subgroup G) =
        (T ⊔ Subgroup.zpowers w).map e.toMonoidHom := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      rfl
    rw [hmap, Subgroup.card_map_of_injective e.injective, hcard,
      Subgroup.card_map_of_injective e.injective]
  · intro R hR hR1
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
      ext z; simp
    have hR' : R.map e.symm.toMonoidHom ≤ T := by
      calc R.map e.symm.toMonoidHom ≤ (T.map e.toMonoidHom).map e.symm.toMonoidHom :=
            Subgroup.map_mono hR
        _ = T := by rw [Subgroup.map_map, hcomp, Subgroup.map_id]
    have hR'1 : R.map e.symm.toMonoidHom ≠ ⊥ := fun h =>
      hR1 ((Subgroup.map_eq_bot_iff_of_injective R
        (f := e.symm.toMonoidHom) e.symm.injective).mp h)
    have h1 := hnorm (R.map e.symm.toMonoidHom) hR' hR'1
    have h2 : (Subgroup.normalizer (R.map e.symm.toMonoidHom : Set G)).map e.toMonoidHom =
        Subgroup.normalizer (R : Set G) := by
      rw [Subgroup.map_normalizer_eq_of_bijective _ e.bijective]
      congr 1
      have hcomp' : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by
        ext z; simp
      rw [Subgroup.map_map, hcomp', Subgroup.map_id]
    have h3 := congrArg (fun S : Subgroup G => S.map e.toMonoidHom) h1
    rw [h2, Subgroup.map_sup, MonoidHom.map_zpowers] at h3
    exact h3

private theorem r925_gcd_two_dvd_add_one {q : ℕ} (hq : 1 ≤ q) :
    Nat.gcd (q - 1) 2 ∣ q + 1 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (Nat.gcd_dvd_right (q - 1) 2) with h | h
  · rw [h]; exact one_dvd _
  · rw [h]
    have h2 : 2 ∣ q - 1 := h ▸ Nat.gcd_dvd_left (q - 1) 2
    have heq : q + 1 = (q - 1) + 2 := by omega
    rw [heq]
    exact Nat.dvd_add h2 (dvd_refl 2)

theorem r925_psl2_normalizer_three {F : Type} [Field F] [Finite F]
    {p f : ℕ} [Fact p.Prime] (hp : p ≠ 3) (hF : Nat.card F = p ^ f)
    {D : Subgroup (PSL2MatrixGroup F)} (hD : Nat.card D = 3) :
    ∃ T : Subgroup (PSL2MatrixGroup F), IsCyclic T ∧ D ≤ T ∧
      T ≤ Subgroup.normalizer (D : Set (PSL2MatrixGroup F)) ∧
      Nat.card (Subgroup.normalizer (D : Set (PSL2MatrixGroup F))) = 2 * Nat.card T ∧
      (Nat.card T * Nat.gcd (p ^ f - 1) 2 = p ^ f - 1 ∨
        Nat.card T * Nat.gcd (p ^ f - 1) 2 = p ^ f + 1) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDcyc : IsCyclic D := isCyclic_of_prime_card (p := 3) hD
  haveI : IsCyclic D := hDcyc
  obtain ⟨gD, hgD⟩ := IsCyclic.exists_generator (α := D)
  let x : PSL2MatrixGroup F := gD
  have hxorder : orderOf x = 3 := by
    rw [show x = (gD : PSL2MatrixGroup F) from rfl, Subgroup.orderOf_coe,
      orderOf_eq_card_of_forall_mem_zpowers hgD, hD]
  have hgDtop : (Subgroup.zpowers gD : Subgroup D) = ⊤ :=
    eq_top_iff.mpr fun x _ => hgD x
  have hxD : D = Subgroup.zpowers x := by
    calc D = (⊤ : Subgroup D).map D.subtype := by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = (Subgroup.zpowers gD).map D.subtype := by rw [← hgDtop]
      _ = Subgroup.zpowers x := by rw [MonoidHom.map_zpowers]; rfl
  have hxne : x ≠ 1 := by
    intro hx1
    rw [hx1, orderOf_one] at hxorder
    omega
  let P : Sylow p (PSL2MatrixGroup F) := default
  obtain ⟨U, S, hUcyc, hUcard, hScyc, hScard, hpart⟩ :=
    CFSG.BenderSuzuki.External.huppert_II_8_5_a_psl2_cover hF P
  obtain ⟨U0, wU0, hU0cyc, hU0card, -, -, -, -, hU0cand, hU0norm⟩ :=
    CFSG.BenderSuzuki.External.huppert_II_8_3_split_torus_reflection_data hF
  obtain ⟨S0, wS0, hS0cyc, hS0card, -, -, -, -, hS0cand, hS0norm⟩ :=
    CFSG.BenderSuzuki.External.huppert_II_8_4_nonsplit_torus_reflection_data hF
  obtain ⟨⟨gU, hUalign⟩, ⟨gS, hSalign⟩⟩ :=
    r925_psl2_torus_align hF P hUcyc hUcard hScyc hScard hpart hU0cyc hU0card hS0cyc hS0card
  have hPcard : Nat.card (P : Subgroup (PSL2MatrixGroup F)) = p ^ f := by
    obtain ⟨eP⟩ := CFSG.BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hF P
    rw [← Nat.card_congr eP.toEquiv, Nat.card_congr Multiplicative.toAdd, hF]
  obtain ⟨T₀, hxT₀, hT₀fam⟩ := (hpart x hxne).exists
  rcases hT₀fam with ⟨g, hTg⟩ | ⟨g, hTg⟩ | ⟨g, hTg⟩
  · exfalso
    have hx' : x ∈ (P : Subgroup (PSL2MatrixGroup F)).map
        (MulAut.conj g).toMonoidHom := by
      rw [← hTg]; exact hxT₀
    have h3dvd : 3 ∣ Nat.card ((P : Subgroup (PSL2MatrixGroup F)).map
        (MulAut.conj g).toMonoidHom) := by
      have h := Subgroup.orderOf_dvd_natCard _ hx'
      rwa [hxorder] at h
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hPcard] at h3dvd
    exact hp ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).mp
      (Nat.prime_three.dvd_of_dvd_pow h3dvd)).symm
  · obtain ⟨hTcyc, hTcard, hTnorm⟩ :=
      r925_reflection_transport U0 wU0 hU0cyc hU0cand hU0norm
        ((MulAut.conj gU).symm.trans (MulAut.conj g))
    have hU0back : U0.map (MulAut.conj gU).symm.toMonoidHom = U :=
      (Subgroup.map_symm_eq_iff_map_eq (K := U) (e := MulAut.conj gU)).mpr hUalign.symm
    have he : U0.map ((MulAut.conj gU).symm.trans (MulAut.conj g)).toMonoidHom =
        U.map (MulAut.conj g).toMonoidHom := by
      rw [show ((MulAut.conj gU).symm.trans (MulAut.conj g)).toMonoidHom =
          (MulAut.conj g).toMonoidHom.comp (MulAut.conj gU).symm.toMonoidHom from rfl,
        ← Subgroup.map_map, hU0back]
    have hxT : x ∈ U0.map ((MulAut.conj gU).symm.trans (MulAut.conj g)).toMonoidHom := by
      rw [he, ← hTg]; exact hxT₀
    have hDle : D ≤ U0.map ((MulAut.conj gU).symm.trans (MulAut.conj g)).toMonoidHom := by
      rw [hxD]; exact Subgroup.zpowers_le.mpr hxT
    refine ⟨U0.map ((MulAut.conj gU).symm.trans (MulAut.conj g)).toMonoidHom, hTcyc, hDle,
      ?_, ?_, Or.inl ?_⟩
    · haveI : IsCyclic (U0.map ((MulAut.conj gU).symm.trans (MulAut.conj g)).toMonoidHom) :=
        hTcyc
      have hcent : U0.map ((MulAut.conj gU).symm.trans (MulAut.conj g)).toMonoidHom ≤
          Subgroup.centralizer (D : Set (PSL2MatrixGroup F)) := by
        intro t ht
        rw [Subgroup.mem_centralizer_iff]
        intro d hd
        exact congrArg Subtype.val (mul_comm'
          (⟨d, hDle hd⟩ : ↥(U0.map ((MulAut.conj gU).symm.trans (MulAut.conj g)).toMonoidHom))
          (⟨t, ht⟩ : ↥(U0.map ((MulAut.conj gU).symm.trans (MulAut.conj g)).toMonoidHom)))
      exact hcent.trans (Subgroup.centralizer_le_normalizer (D : Set (PSL2MatrixGroup F)))
    · have hDne : D ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hD]; norm_num
      rw [hTnorm D hDle hDne, hTcard]
    · rw [Subgroup.card_map_of_injective
          ((MulAut.conj gU).symm.trans (MulAut.conj g)).injective, hU0card, hF]
      exact Nat.div_mul_cancel (Nat.gcd_dvd_left (p ^ f - 1) 2)
  · obtain ⟨hTcyc, hTcard, hTnorm⟩ :=
      r925_reflection_transport S0 wS0 hS0cyc hS0cand hS0norm
        ((MulAut.conj gS).symm.trans (MulAut.conj g))
    have hS0back : S0.map (MulAut.conj gS).symm.toMonoidHom = S :=
      (Subgroup.map_symm_eq_iff_map_eq (K := S) (e := MulAut.conj gS)).mpr hSalign.symm
    have he : S0.map ((MulAut.conj gS).symm.trans (MulAut.conj g)).toMonoidHom =
        S.map (MulAut.conj g).toMonoidHom := by
      rw [show ((MulAut.conj gS).symm.trans (MulAut.conj g)).toMonoidHom =
          (MulAut.conj g).toMonoidHom.comp (MulAut.conj gS).symm.toMonoidHom from rfl,
        ← Subgroup.map_map, hS0back]
    have hxT : x ∈ S0.map ((MulAut.conj gS).symm.trans (MulAut.conj g)).toMonoidHom := by
      rw [he, ← hTg]; exact hxT₀
    have hDle : D ≤ S0.map ((MulAut.conj gS).symm.trans (MulAut.conj g)).toMonoidHom := by
      rw [hxD]; exact Subgroup.zpowers_le.mpr hxT
    refine ⟨S0.map ((MulAut.conj gS).symm.trans (MulAut.conj g)).toMonoidHom, hTcyc, hDle,
      ?_, ?_, Or.inr ?_⟩
    · haveI : IsCyclic (S0.map ((MulAut.conj gS).symm.trans (MulAut.conj g)).toMonoidHom) :=
        hTcyc
      have hcent : S0.map ((MulAut.conj gS).symm.trans (MulAut.conj g)).toMonoidHom ≤
          Subgroup.centralizer (D : Set (PSL2MatrixGroup F)) := by
        intro t ht
        rw [Subgroup.mem_centralizer_iff]
        intro d hd
        exact congrArg Subtype.val (mul_comm'
          (⟨d, hDle hd⟩ : ↥(S0.map ((MulAut.conj gS).symm.trans (MulAut.conj g)).toMonoidHom))
          (⟨t, ht⟩ : ↥(S0.map ((MulAut.conj gS).symm.trans (MulAut.conj g)).toMonoidHom)))
      exact hcent.trans (Subgroup.centralizer_le_normalizer (D : Set (PSL2MatrixGroup F)))
    · have hDne : D ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hD]; norm_num
      rw [hTnorm D hDle hDne, hTcard]
    · have hp1 : 1 ≤ p ^ f :=
        Nat.one_le_iff_ne_zero.mpr (pow_ne_zero f (Fact.out : p.Prime).pos.ne')
      rw [Subgroup.card_map_of_injective
          ((MulAut.conj gS).symm.trans (MulAut.conj g)).injective, hS0card, hF]
      exact Nat.div_mul_cancel (r925_gcd_two_dvd_add_one hp1)

private def r925A5c : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

private theorem r925A5c_pow_three : r925A5c ^ 3 = 1 := by decide +kernel

private theorem r925A5c_ne_one : r925A5c ≠ 1 := by decide +kernel

private theorem r925A5c_orderOf : orderOf r925A5c = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime r925A5c_pow_three r925A5c_ne_one

private theorem r925A5c_card : Nat.card (Subgroup.zpowers r925A5c) = 3 := by
  rw [Nat.card_zpowers, r925A5c_orderOf]

private theorem r925A5c_mem_normalizer (σ : alternatingGroup (Fin 5)) :
    σ ∈ Subgroup.normalizer (Subgroup.zpowers r925A5c : Set (alternatingGroup (Fin 5))) ↔
      σ * r925A5c * σ⁻¹ ∈ Subgroup.zpowers r925A5c := by
  constructor
  · intro h
    exact (Subgroup.mem_normalizer_iff.mp h r925A5c).mp (Subgroup.mem_zpowers r925A5c)
  · intro h
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have h1 : (σ * r925A5c * σ⁻¹) ^ m ∈ Subgroup.zpowers r925A5c :=
      Subgroup.zpowers_le.mpr h (Subgroup.zpow_mem_zpowers (σ * r925A5c * σ⁻¹) m)
    simpa [conj_zpow] using h1

private theorem r925A5c_mem_normalizer' (σ : alternatingGroup (Fin 5)) :
    σ ∈ Subgroup.normalizer (Subgroup.zpowers r925A5c : Set (alternatingGroup (Fin 5))) ↔
      σ * r925A5c * σ⁻¹ ∈ (Finset.range 3).image (fun n => r925A5c ^ n) := by
  rw [r925A5c_mem_normalizer,
    (isOfFinOrder_of_finite r925A5c).mem_zpowers_iff_mem_range_orderOf, r925A5c_orderOf]

private theorem r925A5c_card_normalizer :
    Nat.card (Subgroup.normalizer (Subgroup.zpowers r925A5c :
      Set (alternatingGroup (Fin 5)))) = 6 := by
  have e : Nat.card (Subgroup.normalizer (Subgroup.zpowers r925A5c :
      Set (alternatingGroup (Fin 5)))) =
      Nat.card {σ : alternatingGroup (Fin 5) //
        σ * r925A5c * σ⁻¹ ∈ (Finset.range 3).image (fun n => r925A5c ^ n)} :=
    Nat.card_congr (Equiv.subtypeEquivRight r925A5c_mem_normalizer')
  rw [e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

private theorem r925_card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem r925A5_index_not_three (W : Subgroup (alternatingGroup (Fin 5)))
    (hW : Nat.card W = 3) : ¬ 3 ∣ W.index := by
  have h := Subgroup.card_mul_index W
  rw [hW, r925_card_alt5] at h
  intro hdvd
  obtain ⟨k, hk⟩ := hdvd
  rw [hk] at h
  omega

private def r925A5_sylow_three (W : Subgroup (alternatingGroup (Fin 5)))
    (hW : Nat.card W = 3) : Sylow 3 (alternatingGroup (Fin 5)) :=
  (IsPGroup.of_card (n := 1) (by rw [hW]; norm_num)).toSylow (r925A5_index_not_three W hW)

private theorem r925A5_sylow_coe (W : Subgroup (alternatingGroup (Fin 5)))
    (hW : Nat.card W = 3) :
    (r925A5_sylow_three W hW : Subgroup (alternatingGroup (Fin 5))) = W :=
  IsPGroup.toSylow_coe _ _

private theorem r925A5_normalizer_three (K : Subgroup (alternatingGroup (Fin 5)))
    (hK : Nat.card K = 3) :
    Nat.card (Subgroup.normalizer (K : Set (alternatingGroup (Fin 5)))) = 6 := by
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5))
    (r925A5_sylow_three (Subgroup.zpowers r925A5c) r925A5c_card)
    (r925A5_sylow_three K hK)
  have hcoe : (Subgroup.zpowers r925A5c).map (MulAut.conj c).toMonoidHom = K := by
    have h := congrArg
      (fun P : Sylow 3 (alternatingGroup (Fin 5)) => (P : Subgroup (alternatingGroup (Fin 5))))
      hc
    simp only [Sylow.coe_subgroup_smul, r925A5_sylow_coe (Subgroup.zpowers r925A5c) r925A5c_card,
      r925A5_sylow_coe K hK] at h
    rw [← h]
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply, MulAut.conj_symm_apply]
  rw [← hcoe, ← Subgroup.map_equiv_normalizer_eq,
    Subgroup.card_map_of_injective (MulAut.conj c).injective]
  exact r925A5c_card_normalizer

private theorem r925_psl2_card_mul_gcd {F : Type} [Field F] [Finite F] :
    Nat.card (PSL2MatrixGroup F) * Nat.gcd (Nat.card F - 1) 2 =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
  have hcenter : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) =
      Nat.gcd (Nat.card F - 1) 2 := by
    rw [Nat.card_congr
        (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 2)).toEquiv,
      Fintype.card_fin]
    exact CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd 2
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
  rw [CFSG.GorensteinWalter.sl2_card_formula, hcenter] at h
  exact h.symm

private theorem r925_normalizer_card_of_alt5 {G : Type} [Group G] [Finite G]
    {N D : Subgroup G} (hDN : D ≤ N) (hN : N ≃* alternatingGroup (Fin 5))
    (hD : Nat.card D = 3) (hnorm : Subgroup.normalizer (D : Set G) ≤ N) :
    Nat.card (Subgroup.normalizer (D : Set G)) = 6 := by
  let D' : Subgroup (alternatingGroup (Fin 5)) := (D.subgroupOf N).map hN.toMonoidHom
  have hD'card : Nat.card D' = 3 := by
    rw [Subgroup.card_map_of_injective hN.injective]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv).trans hD
  have h6 := r925A5_normalizer_three D' hD'card
  have hcard1 : Nat.card (Subgroup.normalizer (D.subgroupOf N : Set ↥N)) =
      Nat.card (Subgroup.normalizer (D : Set G)) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hDN]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hnorm).toEquiv
  have hcard2 : Nat.card (Subgroup.normalizer (D.subgroupOf N : Set ↥N)) =
      Nat.card (Subgroup.normalizer (D' : Set (alternatingGroup (Fin 5)))) := by
    rw [← Subgroup.card_map_of_injective (f := hN.toMonoidHom) hN.injective,
      Subgroup.map_equiv_normalizer_eq]
  rw [← hcard1, hcard2]
  exact h6

theorem oddIdxProp_psl2 {K : Type} [Group K] [Finite K] {p f : ℕ}
    (hp : p ≠ 3) (hK : LieModel K .PSL 2 p f) : OddIdxProp K := by
  classical
  intro N Y D hNtop hNodd hDcard hDY hYN hnormD hYperf _hNcat
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hadm, F, hFld, hFin, hFcard, ⟨eK⟩⟩ := hK.statedClassicalModel (by decide)
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime p) := ⟨hadm.1⟩
  have hf1 : 1 ≤ f := hadm.2.1
  let φ : K ≃* PSL2MatrixGroup F := eK.trans (CFSG.GH74.GLS.IVK.L2.equivPSL F)
  set N₁ : Subgroup (PSL2MatrixGroup F) := N.map φ.toMonoidHom
  set Y₁ : Subgroup (PSL2MatrixGroup F) := Y.map φ.toMonoidHom
  set D₁ : Subgroup (PSL2MatrixGroup F) := D.map φ.toMonoidHom
  have hN₁top : N₁ ≠ ⊤ := by
    intro h
    apply hNtop
    have h1 := Subgroup.comap_map_eq_self_of_injective (f := φ.toMonoidHom) φ.injective N
    rw [show N.map φ.toMonoidHom = ⊤ from h, Subgroup.comap_top] at h1
    exact h1.symm
  have hN₁odd : Odd N₁.index := by
    have h := Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective N
    rw [show N₁ = N.map φ.toMonoidHom from rfl, h]
    exact hNodd
  have hD₁card : Nat.card D₁ = 3 := by
    rw [show D₁ = D.map φ.toMonoidHom from rfl,
      Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective, hDcard]
  have hD₁Y₁ : D₁ ≤ Y₁ := Subgroup.map_mono hDY
  have hY₁N₁ : Y₁ ≤ N₁ := Subgroup.map_mono hYN
  have hD₁N₁ : D₁ ≤ N₁ := hD₁Y₁.trans hY₁N₁
  have hnorm₁ : Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F)) ≤ N₁ := by
    have h := Subgroup.map_mono (f := φ.toMonoidHom) hnormD
    rw [Subgroup.map_equiv_normalizer_eq] at h
    exact h
  have hY₁perf : IsPerfA5Cover ↥Y₁ :=
    hYperf.of_mulEquiv (Subgroup.equivMapOfInjective Y φ.toMonoidHom φ.injective)
  have hY₁ne : Y₁ ≠ ⊥ := by
    intro h
    obtain ⟨D', hD'Y, hD'card⟩ := hY₁perf.exists_subgroup_card_three
    have hbot : D' = ⊥ := le_bot_iff.mp (h ▸ hD'Y)
    rw [hbot, Subgroup.card_bot] at hD'card
    omega
  haveI : Nontrivial ↥Y₁ := (Subgroup.nontrivial_iff_ne_bot Y₁).mpr hY₁ne
  haveI : Group.IsPerfect ↥Y₁ := Group.isPerfect_def.mpr hY₁perf.1
  have hY₁nsolv : ¬ Group.IsSolvable ↥Y₁ := Group.IsPerfect.not_isSolvable ↥Y₁
  have hN₁nsolv : ¬ Group.IsSolvable ↥N₁ := by
    intro hsol
    haveI : Group.IsSolvable ↥N₁ := hsol
    haveI : Group.IsSolvable ↥(Y₁.subgroupOf N₁) := inferInstance
    exact hY₁nsolv (Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe hY₁N₁).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hY₁N₁).surjective)
  have hdvdK : Nat.card N₁ ∣ Nat.card (PSL2MatrixGroup F) := by
    simpa using Subgroup.card_dvd_of_le (H := N₁) (K := ⊤) le_top
  have hPSL := r925_psl2_card_mul_gcd (F := F)
  rw [hFcard] at hPSL
  rcases CFSG.GH74.GLS.IVK.Proofs2.nonsolvable_cases hFcard N₁ hN₁nsolv with
    ⟨⟨hA5⟩, -⟩ | ⟨m, hmf, ⟨hPSLq⟩⟩ | ⟨m, h2mf, ⟨hPGLq⟩⟩
  ·
    exfalso
    have hcardN : Nat.card N₁ = 60 := (Nat.card_congr hA5.toEquiv).trans r925_card_alt5
    by_cases hp2 : p = 2
    · subst hp2
      have hodd : Odd (2 ^ f - 1) :=
        Nat.Even.sub_odd Nat.one_le_two_pow
          ((even_two : Even (2 : ℕ)).pow_of_ne_zero (by omega : f ≠ 0)) odd_one
      have hgcd : Nat.gcd (2 ^ f - 1) 2 = 1 := hodd.coprime_two_right.gcd_eq_one
      have hKcard : Nat.card (PSL2MatrixGroup F) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
        simpa [hgcd] using hPSL
      have hLag : Nat.card N₁ * N₁.index = Nat.card (PSL2MatrixGroup F) :=
        Subgroup.card_mul_index N₁
      have hcop : Nat.Coprime (2 ^ f) N₁.index :=
        (Nat.coprime_pow_left_iff (by omega : 0 < f) 2 _).mpr
          (Odd.coprime_two_left hN₁odd)
      have hqdvdN : 2 ^ f ∣ Nat.card N₁ :=
        hcop.dvd_of_dvd_mul_right (by rw [hLag]; exact ⟨(2 ^ f) ^ 2 - 1, hKcard⟩)
      have hdvd60 : 2 ^ f ∣ 60 := by rw [hcardN] at hqdvdN; exact hqdvdN
      have hf2 : f ≤ 2 := by
        by_contra h
        have h3 : 3 ≤ f := by omega
        have h8 : 8 ∣ 2 ^ f := by
          have := Nat.pow_dvd_pow 2 h3
          simpa using this
        exact absurd (h8.trans hdvd60) (by norm_num)
      have hf_ne_one : f ≠ 1 := fun h1 => hadm.2.2.2.1 (by rw [h1, pow_one])
      have hf2' : 2 ≤ f := by omega
      have hf_eq : f = 2 := by omega
      have hK60 : Nat.card (PSL2MatrixGroup F) = 60 := by
        rw [hKcard, hf_eq]; norm_num
      exact hN₁top (Subgroup.eq_top_of_card_eq N₁ (by rw [hcardN, hK60]))
    ·
      have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
      have hgcd : Nat.gcd (p ^ f - 1) 2 = 2 := by
        obtain ⟨k, hk⟩ := hpodd.pow (n := f)
        exact Nat.gcd_eq_right ⟨k, by omega⟩
      have hν6 : Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F))) = 6 :=
        r925_normalizer_card_of_alt5 hD₁N₁ hA5 hD₁card hnorm₁
      obtain ⟨T, hTcyc, hD₁T, hTN, hNcard, hTcard⟩ :=
        r925_psl2_normalizer_three hp hFcard hD₁card
      rw [hgcd] at hTcard
      have hν : Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F))) = p ^ f - 1 ∨
          Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F))) = p ^ f + 1 := by
        rcases hTcard with h | h
        · left; rw [hNcard]; omega
        · right; rw [hNcard]; omega
      have hK2 : Nat.card (PSL2MatrixGroup F) * 2 = p ^ f * ((p ^ f) ^ 2 - 1) := by
        simpa [hgcd] using hPSL
      have hdvd : 60 ∣ Nat.card (PSL2MatrixGroup F) := by
        rw [← hcardN]; exact hdvdK
      rcases hν with h | h
      · rw [hν6] at h
        have hq7 : p ^ f = 7 := by omega
        rw [hq7] at hK2
        have h336 : (7 : ℕ) * (7 ^ 2 - 1) = 336 := by norm_num
        rw [h336] at hK2
        obtain ⟨k, hk⟩ := hdvd
        rw [hk] at hK2
        omega
      · rw [hν6] at h
        have hq5 : p ^ f = 5 := by omega
        rw [hq5] at hK2
        have h120 : (5 : ℕ) * (5 ^ 2 - 1) = 120 := by norm_num
        rw [h120] at hK2
        have hK60 : Nat.card (PSL2MatrixGroup F) = 60 := by omega
        exact hN₁top (Subgroup.eq_top_of_card_eq N₁ (by rw [hcardN, hK60]))
  ·
    exfalso
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact absurd (Nat.eq_zero_of_zero_dvd hmf) (by omega)
    by_cases hp2 : p = 2
    · subst hp2
      have hodd : Odd (2 ^ f - 1) :=
        Nat.Even.sub_odd Nat.one_le_two_pow
          ((even_two : Even (2 : ℕ)).pow_of_ne_zero (by omega : f ≠ 0)) odd_one
      have hgcd : Nat.gcd (2 ^ f - 1) 2 = 1 := hodd.coprime_two_right.gcd_eq_one
      have hKcard : Nat.card (PSL2MatrixGroup F) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
        simpa [hgcd] using hPSL
      have hLag : Nat.card N₁ * N₁.index = Nat.card (PSL2MatrixGroup F) :=
        Subgroup.card_mul_index N₁
      have hcop : Nat.Coprime (2 ^ f) N₁.index :=
        (Nat.coprime_pow_left_iff (by omega : 0 < f) 2 _).mpr
          (Odd.coprime_two_left hN₁odd)
      have hqdvdN : 2 ^ f ∣ Nat.card N₁ :=
        hcop.dvd_of_dvd_mul_right (by rw [hLag]; exact ⟨(2 ^ f) ^ 2 - 1, hKcard⟩)
      have hcardN : Nat.card N₁ = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
        rw [Nat.card_congr hPSLq.toEquiv, CFSG.Walter.psl2_even_card hm0]
      have hdvd : 2 ^ f ∣ 2 ^ m * ((2 ^ m) ^ 2 - 1) := by rw [← hcardN]; exact hqdvdN
      have hoddm : Odd ((2 ^ m) ^ 2 - 1) :=
        Nat.Even.sub_odd
          (by have h : 0 < (2 ^ m) ^ 2 := pow_pos (pow_pos (by norm_num) m) 2; omega)
          (((even_two : Even (2 : ℕ)).pow_of_ne_zero (by omega : m ≠ 0)).pow_of_ne_zero
            (by norm_num : (2 : ℕ) ≠ 0)) odd_one
      have hcop2 : Nat.Coprime (2 ^ f) ((2 ^ m) ^ 2 - 1) :=
        (Nat.coprime_pow_left_iff (by omega : 0 < f) 2 _).mpr
          (Nat.coprime_two_left.mpr hoddm)
      have h2m : 2 ^ f ∣ 2 ^ m := hcop2.dvd_of_dvd_mul_right hdvd
      have hfm : f ≤ m := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h2m
      have hmf' : m ≤ f := Nat.le_of_dvd (by omega) hmf
      have hmf_eq : m = f := le_antisymm hmf' hfm
      have hKcard' : Nat.card (PSL2MatrixGroup F) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
        rw [hKcard, ← hmf_eq]
      exact hN₁top (Subgroup.eq_top_of_card_eq N₁ (by rw [hcardN, hKcard']))
    ·
      have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
      have hgcd_f : Nat.gcd (p ^ f - 1) 2 = 2 := by
        obtain ⟨k, hk⟩ := hpodd.pow (n := f)
        exact Nat.gcd_eq_right ⟨k, by omega⟩
      have hgcd_m : Nat.gcd (p ^ m - 1) 2 = 2 := by
        obtain ⟨k, hk⟩ := hpodd.pow (n := m)
        exact Nat.gcd_eq_right ⟨k, by omega⟩
      have hN2 : Nat.card N₁ * 2 = p ^ m * ((p ^ m) ^ 2 - 1) := by
        rw [Nat.card_congr hPSLq.toEquiv]
        have hgal : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
        have h := r925_psl2_card_mul_gcd (F := GaloisField p m)
        rw [hgal, hgcd_m] at h
        exact h
      have hK2 : Nat.card (PSL2MatrixGroup F) * 2 = p ^ f * ((p ^ f) ^ 2 - 1) := by
        simpa [hgcd_f] using hPSL
      obtain ⟨T, hTcyc, hD₁T, hTN, hNcard, hTcard⟩ :=
        r925_psl2_normalizer_three hp hFcard hD₁card
      rw [hgcd_f] at hTcard
      have hν : Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F))) = p ^ f - 1 ∨
          Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F))) = p ^ f + 1 := by
        rcases hTcard with h | h
        · left; rw [hNcard]; omega
        · right; rw [hNcard]; omega
      have hνcopp : Nat.Coprime
          (Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F)))) p := by
        have hminus : Nat.Coprime (p ^ f - 1) p := by
          refine ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr
            (fun hdiv => ?_)).symm
          have hpq : p ∣ p ^ f := dvd_pow_self p (by omega : f ≠ 0)
          have hp1 : 1 ≤ p ^ f := by
            have := pow_pos (Fact.out : p.Prime).pos f
            omega
          have h1 : p ∣ 1 := by
            have hd := Nat.dvd_sub hpq hdiv
            rw [Nat.sub_sub_self hp1] at hd
            exact hd
          exact (Fact.out : p.Prime).not_dvd_one h1
        have hplus : Nat.Coprime (p ^ f + 1) p := by
          refine ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr
            (fun hdiv => ?_)).symm
          have hpq : p ∣ p ^ f := dvd_pow_self p (by omega : f ≠ 0)
          have h1 : p ∣ 1 := by
            have hd := Nat.dvd_sub hdiv hpq
            have he : p ^ f + 1 - p ^ f = 1 := by omega
            rwa [he] at hd
          exact (Fact.out : p.Prime).not_dvd_one h1
        rcases hν with h | h <;> rw [h] <;> assumption
      have hcop : Nat.Coprime
          (Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F))) * 2) (p ^ m) := by
        rw [Nat.coprime_pow_right_iff (by omega : 0 < m) _ p]
        exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr
          (Nat.Prime.not_dvd_mul (Fact.out : p.Prime)
            ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hνcopp.symm)
            (fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
              Nat.prime_two).mp h2)))).symm
      have hν2dvd : Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F))) * 2 ∣
          (p ^ m) ^ 2 - 1 := by
        have h1 : Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F))) * 2 ∣
            Nat.card N₁ * 2 := Nat.mul_dvd_mul_right (Subgroup.card_dvd_of_le hnorm₁) 2
        rw [hN2, mul_comm (p ^ m) ((p ^ m) ^ 2 - 1)] at h1
        exact hcop.dvd_of_dvd_mul_right h1
      by_cases hmf_eq : m = f
      · have hN_eq : Nat.card N₁ = Nat.card (PSL2MatrixGroup F) := by
          have h1 := hN2
          rw [hmf_eq] at h1
          omega
        exact hN₁top (Subgroup.eq_top_of_card_eq N₁ hN_eq)
      · have h2mf : 2 * m ≤ f := by
          obtain ⟨k, hk⟩ := hmf
          have hk2 : 2 ≤ k := by
            by_contra h
            have hk1 : k ≤ 1 := by omega
            interval_cases k
            · rw [mul_zero] at hk; omega
            · rw [mul_one] at hk; exact hmf_eq hk.symm
          rw [hk]
          nlinarith
        have hpow : (p ^ m) ^ 2 ≤ p ^ f := by
          rw [← pow_mul]
          exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega : m * 2 ≤ f)
        have hν_ge : p ^ f - 1 ≤
            Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F))) := by
          rcases hν with h | h <;> omega
        have hν2_le : Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F))) * 2 ≤
            (p ^ m) ^ 2 - 1 :=
          Nat.le_of_dvd (by
            have hm2 : 1 < p ^ m := Nat.one_lt_pow (by omega : m ≠ 0)
              (by exact (Fact.out : p.Prime).one_lt)
            exact Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num : (2 : ℕ) ≠ 0) hm2))
            hν2dvd
        have hA2 : 2 ≤ p ^ f := Nat.one_lt_pow (by omega : f ≠ 0)
          (by exact (Fact.out : p.Prime).one_lt)
        have h3 : 2 * (p ^ f - 1) ≤ p ^ f - 1 := by
          have h1 : 2 * (p ^ f - 1) ≤
              Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F))) * 2 := by
            omega
          exact le_trans h1 (le_trans hν2_le (Nat.sub_le_sub_right hpow 1))
        omega
  ·
    exfalso
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero, zero_dvd_iff] at h2mf
      omega
    by_cases hp2 : p = 2
    · subst hp2
      have hodd : Odd (2 ^ f - 1) :=
        Nat.Even.sub_odd Nat.one_le_two_pow
          ((even_two : Even (2 : ℕ)).pow_of_ne_zero (by omega : f ≠ 0)) odd_one
      have hgcd : Nat.gcd (2 ^ f - 1) 2 = 1 := hodd.coprime_two_right.gcd_eq_one
      have hKcard : Nat.card (PSL2MatrixGroup F) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
        simpa [hgcd] using hPSL
      have hLag : Nat.card N₁ * N₁.index = Nat.card (PSL2MatrixGroup F) :=
        Subgroup.card_mul_index N₁
      have hcop : Nat.Coprime (2 ^ f) N₁.index :=
        (Nat.coprime_pow_left_iff (by omega : 0 < f) 2 _).mpr
          (Odd.coprime_two_left hN₁odd)
      have hqdvdN : 2 ^ f ∣ Nat.card N₁ :=
        hcop.dvd_of_dvd_mul_right (by rw [hLag]; exact ⟨(2 ^ f) ^ 2 - 1, hKcard⟩)
      have hcardN : Nat.card N₁ = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
        rw [Nat.card_congr hPGLq.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula,
          GaloisField.card 2 m hm0]
      have hdvd : 2 ^ f ∣ 2 ^ m * ((2 ^ m) ^ 2 - 1) := by rw [← hcardN]; exact hqdvdN
      have hoddm : Odd ((2 ^ m) ^ 2 - 1) :=
        Nat.Even.sub_odd
          (by have h : 0 < (2 ^ m) ^ 2 := pow_pos (pow_pos (by norm_num) m) 2; omega)
          (((even_two : Even (2 : ℕ)).pow_of_ne_zero (by omega : m ≠ 0)).pow_of_ne_zero
            (by norm_num : (2 : ℕ) ≠ 0)) odd_one
      have hcop2 : Nat.Coprime (2 ^ f) ((2 ^ m) ^ 2 - 1) :=
        (Nat.coprime_pow_left_iff (by omega : 0 < f) 2 _).mpr
          (Nat.coprime_two_left.mpr hoddm)
      have h2m : 2 ^ f ∣ 2 ^ m := hcop2.dvd_of_dvd_mul_right hdvd
      have hfm : f ≤ m := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h2m
      obtain ⟨k, hk⟩ := h2mf
      have hm_lt_f : m < f := by
        have hkpos : 0 < k := by
          by_contra h
          have hk0 : k = 0 := by omega
          rw [hk0, mul_zero] at hk
          omega
        rw [hk]
        nlinarith [Nat.pos_of_ne_zero hm0]
      omega
    ·
      have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
      have hgcd_f : Nat.gcd (p ^ f - 1) 2 = 2 := by
        obtain ⟨k, hk⟩ := hpodd.pow (n := f)
        exact Nat.gcd_eq_right ⟨k, by omega⟩
      have hcardN : Nat.card N₁ = p ^ m * ((p ^ m) ^ 2 - 1) := by
        rw [Nat.card_congr hPGLq.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula,
          GaloisField.card p m hm0]
      obtain ⟨T, hTcyc, hD₁T, hTN, hNcard, hTcard⟩ :=
        r925_psl2_normalizer_three hp hFcard hD₁card
      rw [hgcd_f] at hTcard
      have hν : Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F))) = p ^ f - 1 ∨
          Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F))) = p ^ f + 1 := by
        rcases hTcard with h | h
        · left; rw [hNcard]; omega
        · right; rw [hNcard]; omega
      have hνcopp : Nat.Coprime
          (Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F)))) p := by
        have hminus : Nat.Coprime (p ^ f - 1) p := by
          refine ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr
            (fun hdiv => ?_)).symm
          have hpq : p ∣ p ^ f := dvd_pow_self p (by omega : f ≠ 0)
          have hp1 : 1 ≤ p ^ f := by
            have := pow_pos (Fact.out : p.Prime).pos f
            omega
          have h1 : p ∣ 1 := by
            have hd := Nat.dvd_sub hpq hdiv
            rw [Nat.sub_sub_self hp1] at hd
            exact hd
          exact (Fact.out : p.Prime).not_dvd_one h1
        have hplus : Nat.Coprime (p ^ f + 1) p := by
          refine ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr
            (fun hdiv => ?_)).symm
          have hpq : p ∣ p ^ f := dvd_pow_self p (by omega : f ≠ 0)
          have h1 : p ∣ 1 := by
            have hd := Nat.dvd_sub hdiv hpq
            have he : p ^ f + 1 - p ^ f = 1 := by omega
            rwa [he] at hd
          exact (Fact.out : p.Prime).not_dvd_one h1
        rcases hν with h | h <;> rw [h] <;> assumption
      have hcop : Nat.Coprime
          (Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F)))) (p ^ m) :=
        (Nat.coprime_pow_right_iff (by omega : 0 < m) _ p).mpr hνcopp
      have hνdvd : Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F))) ∣
          (p ^ m) ^ 2 - 1 := by
        have h1 : Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F))) ∣
            Nat.card N₁ := Subgroup.card_dvd_of_le hnorm₁
        rw [hcardN, mul_comm (p ^ m) ((p ^ m) ^ 2 - 1)] at h1
        exact hcop.dvd_of_dvd_mul_right h1
      have hpow : (p ^ m) ^ 2 ≤ p ^ f := by
        obtain ⟨k, hk⟩ := h2mf
        have hkpos : 1 ≤ k := by
          by_contra h
          have hk0 : k = 0 := by omega
          rw [hk0, mul_zero] at hk
          omega
        have hmk : m * 2 ≤ f := by
          rw [hk]
          nlinarith [Nat.pos_of_ne_zero hm0, hkpos]
        rw [← pow_mul]
        exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hmk
      have hν_ge : p ^ f - 1 ≤
          Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F))) := by
        rcases hν with h | h <;> omega
      have hq0ge : 5 ≤ p ^ m := by
        have hp5 : 5 ≤ p := (Fact.out : p.Prime).five_le_of_ne_two_of_ne_three hp2 hp
        have h1 : p ^ 1 ≤ p ^ m :=
          Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega : 1 ≤ m)
        exact le_trans hp5 (by simpa using h1)
      have hν_le : Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F))) ≤
          (p ^ m) ^ 2 - 1 :=
        Nat.le_of_dvd (by
          have h1 : 1 < (p ^ m) ^ 2 := by nlinarith [hq0ge]
          exact Nat.sub_pos_of_lt h1) hνdvd
      have hν_eq : Nat.card (Subgroup.normalizer (D₁ : Set (PSL2MatrixGroup F))) =
          p ^ f - 1 := by omega
      have hA1 : 1 ≤ p ^ f := by
        have := pow_pos (Fact.out : p.Prime).pos f
        omega
      have hB1 : 1 ≤ (p ^ m) ^ 2 := by nlinarith [hq0ge]
      have hq_eq : p ^ f = (p ^ m) ^ 2 := by omega
      have hT2 : Nat.card T * 2 = p ^ f - 1 := by omega
      have hT2' : 2 * Nat.card T + 1 = (p ^ m) ^ 2 := by omega
      have hTN₁ : T ≤ N₁ := hTN.trans hnorm₁
      obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := T)
      have hxord : orderOf x = Nat.card T := orderOf_eq_card_of_forall_mem_zpowers hx
      let x' : Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m) :=
        hPGLq ⟨(x : PSL2MatrixGroup F), hTN₁ x.2⟩
      have hx'ord : orderOf x' = Nat.card T := by
        rw [← hxord]
        exact (MulEquiv.orderOf_eq hPGLq ⟨(x : PSL2MatrixGroup F), hTN₁ x.2⟩).trans
          ((Subgroup.orderOf_coe (⟨(x : PSL2MatrixGroup F), hTN₁ x.2⟩ : N₁)).symm.trans
            (Subgroup.orderOf_coe x))
      have hle := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.pgl2_orderOf_le
        (GaloisField p m) x'
      rw [GaloisField.card p m hm0, hx'ord] at hle
      nlinarith [hle, hT2', hq0ge]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
