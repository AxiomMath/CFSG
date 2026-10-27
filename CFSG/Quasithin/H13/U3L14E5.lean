module

public import CFSG.Quasithin.H13.U3L14Blk
public import CFSG.Quasithin.H13.U3L14L3
public import CFSG.Quasithin.H13.U3L14G2
public import CFSG.Quasithin.H13.A5R1Frame
public import CFSG.Quasithin.H13.A5RawNat

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem kplus_factor {K : Subgroup G} (hD : KData14 T L V V₂ Lp K)
    (hA5 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))) {x : G} (hx : x ∈ Lp)
    (hxo : Odd (orderOf x)) (hx1 : x ≠ 1) :
    ¬ ∀ t ∈ T ⊓ K, t⁻¹ * (x * t * x⁻¹) ∈ pCoreOf 2 K := by
  intro hfix
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀⟩ := hA5
  let e : (↥K ⧸ (pCoreOf 2 K).subgroupOf K) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq (pCoreOf_subgroupOf_eq K)).trans e₀
  have hx3 : x ^ 3 = 1 := S.odd_pow_three hx hxo
  set α := kAct K ⟨x, hD.Lp_K hx⟩ with hα
  have hα1 : α ≠ 1 := S.kAct_ne_one hD hx hxo hx1
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨x, hD.Lp_K hx⟩ : ↥(normalizer (K : Set G))) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  obtain ⟨hP2, hPi⟩ := S.sylowImage hD
  set π := QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K) with hπ
  set P := ((T ⊓ K).subgroupOf K).map π with hP
  have hcard : Nat.card (↥K ⧸ (pCoreOf 2 K).subgroupOf K) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hPne : P ≠ ⊥ := by
    intro h
    apply hPi
    rw [h, index_bot, hcard]
    norm_num
  have hP2d : 2 ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP2
    rw [hn]
    rcases n with _ | n
    · exfalso
      apply hPne
      rw [← card_eq_one, hn, pow_zero]
    · exact dvd_pow_self 2 (by omega)
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card' 2 hP2d
  obtain ⟨t, ht, htτ⟩ := τ.2
  have hατ : α (τ : ↥K ⧸ (pCoreOf 2 K).subgroupOf K) = τ := by
    rw [← htτ, hα, hπ, QuotientGroup.mk'_apply]
    have htTK : (t : G) ∈ T ⊓ K := mem_subgroupOf.mp ht
    exact (CFSG.SignalizerFunctorTheorem.sectionAction_mk_eq_iff le_rfl
      (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K) _ t).2 (hfix t htTK)
  set α' := MulAut.congr e α with hα'
  have hα'3 : α' ^ 3 = 1 := by rw [hα', ← map_pow, hα3, map_one]
  have hτ1 : (τ : ↥K ⧸ (pCoreOf 2 K).subgroupOf K) ≠ 1 := by
    intro h
    have : τ = 1 := Subtype.ext h
    rw [this, orderOf_one] at hτ
    exact absurd hτ (by norm_num)
  have hτ2 : (τ : ↥K ⧸ (pCoreOf 2 K).subgroupOf K) ^ 2 = 1 := by
    have h1 : τ ^ 2 = 1 := by
      have h0 := pow_orderOf_eq_one τ
      rwa [hτ] at h0
    simpa using congrArg Subtype.val h1
  have h1 := mulAut_alt5_eq_one hα'3 (τ := e τ) (fun h => hτ1 (e.injective (h.trans
    (map_one e).symm))) (by rw [← map_pow, hτ2, map_one])
    (by simp only [hα', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hατ])
  apply hα1
  have : α = (MulAut.congr e).symm α' := by rw [hα', MulEquiv.symm_apply_apply]
  rw [this, h1, map_one]

theorem exists_I (h1332 : Stmt13_3_2) {K : Subgroup G} (hD : KData14 T L V V₂ Lp K)
    (hA5 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))) :
    ∃ I : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T I ∧
      I ⊓ centralizer (K : Set G) = ⊥ ∧ T ≤ normalizer (I : Set G) ∧ IsElemAbelian 2 I ∧
      normalizer (I : Set G) ≤ normalizer (K : Set G) ∧ Nonempty (A5.Frame T K I) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨hTN, -, -, huniq⟩, ⟨⟨I, hI⟩, hall⟩, -⟩ := h1332 G T L S.h13 K hD.faithful
  obtain ⟨-, hTI, -, hIc, hmod⟩ := hall I hI
  have hKI : K ≤ normalizer (I : Set G) := hI.2.2.1
  have hIe : IsElemAbelian 2 I := ⟨hIc, fun v hv => (mem_reducedAggregate' (hI.1 hv)).2.2⟩
  have hKn : (K.subgroupOf (K ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).2 (sup_le le_normalizer hD.T_K)
  have hO : pCoreOf 2 K ≤ centralizer (I : Set G) := by
    have h1 : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ T) :=
      CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K _ le_sup_left hKn
    intro k hk
    rw [mem_centralizer_iff]
    intro v hv
    exact ((mem_reducedAggregate' (hI.1 hv)).2.1 k (h1 hk)).symm
  obtain ⟨e₀⟩ := hA5
  have hcard : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 60 := by
    rw [Nat.card_congr e₀.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hle := card_autOn_le_card_quot hKI hO
  rw [hcard] at hle
  rcases hmod with ⟨hnat, hZ⟩ | ⟨hnat, -⟩ | ⟨-, -, hreal⟩ | ⟨hlin, -, -⟩ | ⟨hu, -, -⟩
  ·
    have hNL : normalizer (I : Set G) ≤ normalizer (K : Set G) := by
      have hI2 : IsPGroup 2 I := fun v => ⟨1, Subtype.ext (by simpa using hIe.2 v v.2)⟩
      obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
        (⟨I, hI.2.1, hI2, rfl⟩ : IsTwoLocal (normalizer (I : Set G)))
      have := huniq M' hM' ((sup_le hKI hTI).trans hM'le)
      exact this ▸ hM'le
    have hsyl : IsSylowTwoOf (T ⊓ K) K :=
      isSylowTwoOf_inf_of_le_normalizer (S.syl (le_sup_right : T ≤ K ⊔ T)) le_sup_left
        (sup_le le_normalizer hD.T_K)
    obtain ⟨R⟩ := A5.exists_rawData5_of_nat hKI hnat
    obtain ⟨F⟩ := A5.exists_frame R hNL S.isP_T hTI hsyl
    exact ⟨I, hI, hZ, hTI, hIe, hNL, ⟨F⟩⟩
  ·
    obtain ⟨e6⟩ := A6.nonempty_mulEquiv_of_realizes (A6.altDn_faithful (by norm_num)) hnat
    rw [Nat.card_congr e6.toEquiv] at hle
    change Nat.card ↥(alternatingGroup (Fin 6)) ≤ 60 at hle
    rw [nat_card_alternatingGroup, Nat.card_fin] at hle
    exact absurd hle (by decide)
  · obtain ⟨e6⟩ := A6.nonempty_mulEquiv_of_realizes (A6.altCoreModel_faithful (by norm_num)) hreal
    rw [Nat.card_congr e6.toEquiv] at hle
    change Nat.card ↥(alternatingGroup (Fin 6)) ≤ 60 at hle
    rw [nat_card_alternatingGroup, Nat.card_fin] at hle
    exact absurd hle (by decide)
  · obtain ⟨e⟩ := nonempty_mulEquiv_sl_two_of_lieModel hlin
    rw [Nat.card_congr e.toEquiv, card_sl_three_zmod_two] at hcard
    exact absurd hcard (by norm_num)
  · rw [card_of_statedClassicalModel_psu_three_three
      (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hu)] at hcard
    exact absurd hcard (by norm_num)

end Set14

omit [Finite G] in
theorem inf_centralizer_le {K I : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K))
    (hA5 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hKI : K ≤ normalizer (I : Set G)) (hO : pCoreOf 2 K ≤ centralizer (I : Set G))
    (hZ : I ⊓ centralizer (K : Set G) = ⊥) (hI1 : I ≠ ⊥) :
    K ⊓ centralizer (I : Set G) ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (A3.pCore_eq_openCore 2 ↥K)).symm
      (A3.isQuasisimple_iff_open.2 hq)
  set N := K ⊓ centralizer (I : Set G) with hN
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hNn : (N.subgroupOf K).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun k hk =>
      mem_normalizer_inf (le_normalizer hk) (mem_normalizer_centralizer (hKI hk))
  have hN'n : ((N.subgroupOf K).map π).Normal := hNn.map π (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hN'n with htop | hcen
  · exfalso
    apply hI1
    rw [eq_bot_iff, ← hZ]
    intro v hv
    refine mem_inf.mpr ⟨hv, mem_centralizer_iff.mpr fun k hk => ?_⟩
    have hmem : π ⟨k, hk⟩ ∈ (N.subgroupOf K).map π := htop ▸ mem_top _
    obtain ⟨n, hnN, hne⟩ := hmem
    have h1 : n⁻¹ * ⟨k, hk⟩ ∈ CFSG.pCore 2 ↥K := QuotientGroup.eq.mp hne
    have h2 : ((n⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ centralizer (I : Set G) :=
      hO (coe_mem_pCoreOf_iff.2 h1)
    have h3 : (n : G) ∈ centralizer (I : Set G) := (mem_inf.mp (mem_subgroupOf.mp hnN)).2
    have h4 : k ∈ centralizer (I : Set G) := by
      have : k = (n : G) * ((n⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by simp
      rw [this]
      exact mul_mem h3 h2
    exact (mem_centralizer_iff.mp h4 v hv).symm
  ·
    obtain ⟨e⟩ := hA5
    have hZ1 : center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have h1 : e z ∈ center (alternatingGroup (Fin 5)) := by
        rw [mem_center_iff] at hz ⊢
        intro g
        obtain ⟨g', rfl⟩ := e.surjective g
        rw [← map_mul, ← map_mul, hz g']
      rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at h1
      rw [mem_bot]
      exact e.injective (h1.trans (map_one e).symm)
    intro n hn
    have hnK : n ∈ K := (mem_inf.mp hn).1
    have h1 : π ⟨n, hnK⟩ ∈ center (↥K ⧸ CFSG.pCore 2 ↥K) :=
      hcen ⟨⟨n, hnK⟩, mem_subgroupOf.mpr hn, rfl⟩
    rw [hZ1, mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact coe_mem_pCoreOf_iff.2 h1

theorem InD_of_InK4 : ∀ σ : Equiv.Perm (Fin 5), A5.InK4 σ → A5.InD σ := by decide +kernel

theorem card_K4Frame : Nat.card A5.K4Frame = 4 := by
  have : Fintype.card {σ : Equiv.Perm (Fin 5) // A5.InK4 σ} = 4 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem inf_centralizer_eq {K I : Subgroup G} (hD : KData14 T L V V₂ Lp K)
    (hI : IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T I) (hTI : T ≤ normalizer (I : Set G))
    (hCK : K ⊓ centralizer (I : Set G) ≤ pCoreOf 2 K) :
    T ⊓ centralizer (I : Set G) = pCoreOf 2 (K ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOT : pCoreOf 2 (K ⊔ T) ≤ T :=
    pCoreOf_two_le_of_sylowIn le_sup_right (S.syl (le_sup_right : T ≤ K ⊔ T)).2.1
      (S.syl (le_sup_right : T ≤ K ⊔ T)).2.2
  apply le_antisymm
  ·
    have hKTI : K ⊔ T ≤ normalizer (I : Set G) := sup_le hI.2.2.1 hTI
    have h2 : IsPGroup 2 ↥((K ⊔ T) ⊓ centralizer (I : Set G)) := by
      intro d
      obtain ⟨m, hm⟩ := pow_two_mem_of_sup hD.T_K S.isP_T (mem_inf.mp d.2).1
      have hmC : (d : G) ^ 2 ^ m ∈ centralizer (I : Set G) := pow_mem (mem_inf.mp d.2).2 _
      obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 K
        ⟨_, hCK (mem_inf.mpr ⟨hm, hmC⟩)⟩
      refine ⟨m + k, Subtype.ext ?_⟩
      have : ((d : G) ^ 2 ^ m) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      simpa [pow_add, pow_mul] using this
    have hle : (K ⊔ T) ⊓ centralizer (I : Set G) ≤ pCoreOf 2 (K ⊔ T) :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun y hy => mem_normalizer_inf (le_normalizer hy)
          (mem_normalizer_centralizer (hKTI hy))) h2
    exact (inf_le_inf_right _ le_sup_right).trans hle
  · refine le_inf hOT fun k hk => mem_centralizer_iff.mpr fun v hv => ?_
    exact ((mem_reducedAggregate' (hI.1 hv)).2.1 k hk).symm

theorem relIndex_inf_eq_four {K : Subgroup G} (hD : KData14 T L V V₂ Lp K)
    (hA5 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))) :
    (pCoreOf 2 K).relIndex (T ⊓ K) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀⟩ := hA5
  have h60 : (pCoreOf 2 K).relIndex K = 60 := by
    rw [relIndex_pCoreOf_eq_card, Nat.card_congr e₀.toEquiv, nat_card_alternatingGroup,
      Nat.card_fin]
    rfl
  have hsyl : IsSylowTwoOf (T ⊓ K) K :=
    isSylowTwoOf_inf_of_le_normalizer (S.syl (le_sup_right : T ≤ K ⊔ T)) le_sup_left
      (sup_le le_normalizer hD.T_K)
  have h1 := relIndex_mul_relIndex (pCoreOf 2 K) (T ⊓ K) K (S.pCoreOf_K_le hD) inf_le_right
  rw [h60] at h1
  have hodd : ¬ 2 ∣ (T ⊓ K).relIndex K := hsyl.2.2
  have hdvd : (pCoreOf 2 K).relIndex (T ⊓ K) ∣ Nat.card ↥(T ⊓ K) := index_dvd_card _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (S.isP_T.to_le (inf_le_left : T ⊓ K ≤ T))
  rw [hn] at hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hk] at h1 ⊢
  rcases k with _ | _ | _ | k
  · exfalso
    apply hodd
    rw [pow_zero, one_mul] at h1
    rw [h1]
    norm_num
  · exfalso
    apply hodd
    exact ⟨30, by omega⟩
  · rfl
  · exfalso
    have : 8 ∣ 60 := ⟨2 ^ k * (T ⊓ K).relIndex K, by rw [← h1]; ring⟩
    norm_num at this

theorem R1_eq {K I : Subgroup G} (hD : KData14 T L V V₂ Lp K) (hg : ¬ Lp ≤ K)
    (hA5 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))) (F : A5.Frame T K I)
    (hCT : T ⊓ centralizer (I : Set G) = pCoreOf 2 (K ⊔ T))
    (hCK : K ⊓ centralizer (I : Set G) = pCoreOf 2 K) :
    pCoreOf 2 (Lp ⊔ T) = F.R1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (Lp ⊔ T) with hR
  have hTKN : T ⊓ K ≤ normalizer (I : Set G) := inf_le_left.trans F.T_le
  set f : ↥(T ⊓ K) →* Equiv.Perm (Fin 5) := F.ρ.comp (inclusion hTKN) with hf
  have hfrange : f.range = A5.K4Frame := by
    have hle : f.range ≤ A5.K4Frame := by
      rintro _ ⟨k, rfl⟩
      rw [A5.mem_K4Frame]
      refine A5.InK4_of_D_alt _ (F.T_D _ (mem_inf.mp k.2).1) ?_
      exact (F.image_L _).1 ⟨inclusion hTKN k, (mem_inf.mp k.2).2, rfl⟩
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_K4Frame, ← Subgroup.index_ker f]
    show 4 ≤ f.ker.index
    have hker : f.ker = (pCoreOf 2 K).subgroupOf (T ⊓ K) := by
      ext k
      rw [MonoidHom.mem_ker, mem_subgroupOf, ← hCK]
      constructor
      · intro h
        exact mem_inf.mpr ⟨(mem_inf.mp k.2).2, F.mem_centralizer_of_rho _ h⟩
      · intro h
        exact F.rho_eq_one_of_mem _ (mem_inf.mp h).2
    rw [hker]
    show 4 ≤ (pCoreOf 2 K).relIndex (T ⊓ K)
    rw [S.relIndex_inf_eq_four hD hA5]
  have hle : F.R1 ≤ R := by
    intro t ht
    have htT : t ∈ T := F.R1_le_T ht
    have hσ : F.ρ ⟨t, F.T_le htT⟩ ∈ f.range := by
      rw [hfrange, A5.mem_K4Frame]
      exact (F.mem_R1 htT).1 ht
    obtain ⟨k, hk⟩ := hσ
    have hkt : (k : G)⁻¹ * t ∈ T ⊓ centralizer (I : Set G) := by
      refine mem_inf.mpr ⟨mul_mem (inv_mem (mem_inf.mp k.2).1) htT, ?_⟩
      refine F.mem_centralizer_of_rho ⟨(k : G)⁻¹ * t, mul_mem (inv_mem (hTKN k.2)) (F.T_le htT)⟩ ?_
      have : (⟨(k : G)⁻¹ * t, mul_mem (inv_mem (hTKN k.2)) (F.T_le htT)⟩ :
          ↥(normalizer (I : Set G))) = (inclusion hTKN k)⁻¹ * ⟨t, F.T_le htT⟩ := rfl
      rw [this, map_mul, map_inv, ← hk]
      exact inv_mul_cancel _
    rw [hCT] at hkt
    have : t = (k : G) * ((k : G)⁻¹ * t) := by group
    rw [this]
    exact mul_mem (S.inf_le_R1 hD hg k.2) (S.pCoreOf_KT_le_R1 hD hkt)
  set fT : ↥T →* Equiv.Perm (Fin 5) := F.ρ.comp (inclusion F.T_le) with hfT
  have hcomap : F.R1.subgroupOf T = A5.K4Frame.comap fT := by
    ext t
    rw [mem_subgroupOf, mem_comap, A5.mem_K4Frame]
    exact F.mem_R1 t.2
  have hK4T : A5.K4Frame ≤ fT.range := by
    intro σ hσ
    obtain ⟨g, hgT, hg⟩ := F.K4_T σ hσ
    exact ⟨⟨g, hgT⟩, by rw [hfT, MonoidHom.comp_apply, ← hg]; rfl⟩
  have hTD : fT.range ≤ A5.Dsub := by
    rintro _ ⟨t, rfl⟩
    exact F.T_D _ t.2
  have hidx2 : F.R1.relIndex T ≤ 2 := by
    rw [relIndex, hcomap, index_comap]
    have h1 : A5.K4Frame.relIndex A5.Dsub = 2 := by
      have h2 := card_mul_index (A5.K4Frame.subgroupOf A5.Dsub)
      rw [Nat.card_congr (subgroupOfEquivOfLe
          (show A5.K4Frame ≤ A5.Dsub from fun σ hσ => InD_of_InK4 σ hσ)).toEquiv,
        card_K4Frame, A5.card_Dsub] at h2
      rw [relIndex]
      omega
    calc A5.K4Frame.relIndex fT.range ≤ A5.K4Frame.relIndex A5.Dsub :=
          relIndex_le_of_le_right hTD (by rw [h1]; norm_num)
      _ = 2 := h1
  have h3 := relIndex_mul_relIndex F.R1 R T hle S.R1_le_T
  rw [S.index2] at h3
  have h4 : F.R1.relIndex R = 1 := by
    have hpos : 0 < F.R1.relIndex R :=
      Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := F.R1.subgroupOf R))
    omega
  exact le_antisymm (relIndex_eq_one.mp h4) hle

theorem not_normalizer_baum_le {K I : Subgroup G} (hD : KData14 T L V V₂ Lp K) (hg : ¬ Lp ≤ K)
    (hA5 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))) (F : A5.Frame T K I)
    (hIe : IsElemAbelian 2 I) (hIT : I ≤ T)
    (hCT : T ⊓ centralizer (I : Set G) = pCoreOf 2 (K ⊔ T))
    (hCK : K ⊓ centralizer (I : Set G) = pCoreOf 2 K) :
    ¬ normalizer (baum (pCoreOf 2 (Lp ⊔ T)) : Set G) ≤ normalizer (L : Set G) := by
  intro h
  have hB : baum (pCoreOf 2 (Lp ⊔ T)) = baum (pCoreOf 2 (K ⊔ T)) := by
    rw [S.R1_eq hD hg hA5 F hCT hCK, (F.lemma_13_2_4_one hIe hIT).2.2, hCT]
  have hK : K ≤ normalizer (baum (pCoreOf 2 (K ⊔ T)) : Set G) :=
    le_sup_left.trans ((LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ T)).trans
      (normalizer_le_normalizer_baum _))
  rw [← hB] at hK
  exact hD.K_M (hK.trans h)

end Set14

end CFSG.Quasithin.H13.U3
