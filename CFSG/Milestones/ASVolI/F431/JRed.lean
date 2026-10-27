module

public import CFSG.Milestones.ASVolI.F4L3

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

section SylowCard

variable {G : Type} [Group G]

theorem burnsideF4ja_card_conjSub (g : G) (K : Subgroup G) :
    Nat.card (conjSub g K) = Nat.card K :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem burnsideF4ja_conjSub_of_mem {x : G} {H : Subgroup G} (hx : x ∈ H) :
    conjSub x H = H := by
  ext y
  rw [mem_conjSub]
  constructor
  · intro h
    have h' := H.mul_mem (H.mul_mem hx h) (H.inv_mem hx)
    rwa [show x * (x⁻¹ * y * x) * x⁻¹ = y by group] at h'
  · intro h
    exact H.mul_mem (H.mul_mem (H.inv_mem hx) h) hx

theorem burnsideF4ja_isPGroup_zpowers {u : G} (hu : u * u = 1) :
    IsPGroup 2 (Subgroup.zpowers u) := by
  have h2 : u ^ 2 = 1 := by rw [pow_two]; exact hu
  have hdvd : orderOf u ∣ 2 ^ 1 := by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one h2
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])

variable [Finite G]

theorem burnsideF4ja_exists_isSylowOf_ge {K Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQK : Q ≤ K) :
    ∃ S : Subgroup G, ChF.IsSylowOf 2 S K ∧ Q ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(S₀ : Subgroup K).map K.subtype, ⟨Subgroup.map_subtype_le _, S₀.isPGroup'.map _, ?_⟩,
    fun x hx => ⟨⟨x, hQK hx⟩, hS₀ (show (⟨x, hQK hx⟩ : K) ∈ Q.subgroupOf K from hx), rfl⟩⟩
  have h : ((S₀ : Subgroup K).map K.subtype).subgroupOf K = (S₀ : Subgroup K) :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have h' := S₀.not_dvd_index
  rw [← h] at h'
  exact h'

theorem burnsideF4ja_exists_isSylowOf (K : Subgroup G) : ∃ S : Subgroup G, ChF.IsSylowOf 2 S K := by
  obtain ⟨S, hS, -⟩ := burnsideF4ja_exists_isSylowOf_ge (IsPGroup.of_bot (p := 2)) (bot_le : ⊥ ≤ K)
  exact ⟨S, hS⟩

theorem burnsideF4ja_card_le_of_isSylowOf {T H P : Subgroup G} (hT : ChF.IsSylowOf 2 T H)
    (hPH : P ≤ H) (hP : IsPGroup 2 P) : Nat.card P ≤ Nat.card T := by
  obtain ⟨x, -, hx⟩ := F7.isSylowTwoOf_exists_conj_le (T := T) (H := H) hT hPH hP
  calc Nat.card P ≤ Nat.card (conjSub x T) := Subgroup.card_le_of_le hx
    _ = Nat.card T := burnsideF4ja_card_conjSub x T

theorem burnsideF4ja_isSylowOf_of_card_le {T H P : Subgroup G} (hT : ChF.IsSylowOf 2 T H)
    (hPH : P ≤ H) (hP : IsPGroup 2 P) (hc : Nat.card T ≤ Nat.card P) : ChF.IsSylowOf 2 P H := by
  have heq : Nat.card P = Nat.card T :=
    le_antisymm (burnsideF4ja_card_le_of_isSylowOf hT hPH hP) hc
  refine ⟨hPH, hP, ?_⟩
  have h1 := Subgroup.relIndex_mul_card P H
  have h2 := Subgroup.relIndex_mul_card T H
  rw [inf_of_le_left hPH, heq] at h1
  rw [inf_of_le_left hT.1] at h2
  have hrel : P.relIndex H = T.relIndex H :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)
  rw [hrel]
  exact hT.2.2

end SylowCard

section Transport

variable {Mb : Type} [Group Mb] {G : Type} [Group G] {N : Subgroup Mb}

theorem burnsideF4ja_subImg_inf_centralizer {b : ↥N →* G} (hb : Function.Injective b)
    (X : Subgroup Mb) {x : Mb} (hx : x ∈ N) :
    subImg b X ⊓ Subgroup.centralizer ({b ⟨x, hx⟩} : Set G) =
      subImg b (X ⊓ Subgroup.centralizer ({x} : Set Mb)) := by
  ext g
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hg, hgc⟩
    obtain ⟨y, hyN, hyX, rfl⟩ := mem_subImg.mp hg
    refine mem_subImg.mpr ⟨y, hyN, Subgroup.mem_inf.mpr ⟨hyX, ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hgc ⊢
    exact (commute_iff_of_injective hb hx hyN).mp hgc
  · intro hg
    obtain ⟨y, hyN, hyXC, rfl⟩ := mem_subImg.mp hg
    obtain ⟨hyX, hyc⟩ := Subgroup.mem_inf.mp hyXC
    refine ⟨mem_subImg_of_mem b hyN hyX, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
    exact (commute_iff_of_injective hb hx hyN).mpr hyc

end Transport

section F440

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {M : Type} [Group M]

theorem burnsideF4ja_bM_eq (β : Cpl M₁ M₂ Y) (ε : Y →* M) (v : ↥(M₁ ⊓ M₂)) :
    bM β ε v = burnsideF4d_bOne β ε ⟨v, v.2.1⟩ := rfl

theorem burnsideF4ja_bM_injective (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (ε : Y →* M)
    (hε : Function.Injective (epsG β ε)) : Function.Injective (bM β ε) := by
  intro v w h
  rw [burnsideF4ja_bM_eq, burnsideF4ja_bM_eq] at h
  have hb : Function.Injective (burnsideF4d_bOne β ε) := hε.comp (f1_injective β hβ)
  have h' := congrArg Subtype.val (hb h)
  exact Subtype.ext h'

end F440

theorem burnsideF4ja_F_4_40_of (h33 : F_4_33) (h35 : F_4_35) (h38 : F_4_38) : F_4_40 := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL v hvS hv1 hv2 hsyl
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb₁ : Function.Injective (burnsideF4d_bOne β ε) :=
    hyp.inj.comp (f1_injective β hyp.faithful)
  have hbM : Function.Injective (bM β ε) :=
    burnsideF4ja_bM_injective β hyp.faithful ε hyp.inj
  have hSbH : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ M₁ ⊓ M₂ :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right
  have hSbGp : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ Gp :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hSbP : IsPGroup 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hSeq : SinM Gp β ε = subImg (burnsideF4d_bOne β ε) (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) :=
    burnsideF4d_SinM_eq Gp β ε
  obtain ⟨T, hT⟩ := burnsideF4ja_exists_isSylowOf (MiOne β ε ⊓ MiTwo β ε)
  have hS : ChF.IsSylowOf 2 (SinM Gp β ε) ⊤ := by
    have h1 := h33 κ f E Gp M₁ M₂ Y β M ε z hyp T hT
    rwa [(h38 κ f E Gp M₁ M₂ Y β M ε z hyp hL T hT).1] at h1
  obtain ⟨u, hu⟩ : ∃ u : M, bM β ε v = u := ⟨_, rfl⟩
  have hu1 : u ≠ 1 := fun h => hv1 (hbM (by rw [hu, h, map_one]))
  have hu2 : u * u = 1 := by rw [← hu, ← map_mul, hv2, map_one]
  have huC : u ∈ Subgroup.centralizer ({u} : Set M) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨P, hP, hPu⟩ := burnsideF4ja_exists_isSylowOf_ge (burnsideF4ja_isPGroup_zpowers hu2)
    (Subgroup.zpowers_le.mpr huC)
  have huP : u ∈ P := hPu (Subgroup.mem_zpowers u)
  obtain ⟨x, -, hPx⟩ := F7.isSylowTwoOf_exists_conj_le (T := SinM Gp β ε) (H := ⊤) hS le_top
    hP.2.1
  obtain ⟨u', hu'⟩ : ∃ u' : M, u' = x⁻¹ * u * x := ⟨_, rfl⟩
  have hu'S : u' ∈ SinM Gp β ε := by rw [hu']; exact mem_conjSub.mp (hPx huP)
  have hP'S : conjSub x⁻¹ P ≤ SinM Gp β ε ⊓ Subgroup.centralizer ({u'} : Set M) := by
    refine le_inf ?_ ?_
    · have h1 := conjSub_mono x⁻¹ hPx
      rwa [conjSub_conjSub_inv] at h1
    · have h1 := conjSub_mono x⁻¹ hP.1
      rwa [← burnsideF4d_Z1_centralizer_conj, inv_inv, ← hu'] at h1
  rw [hSeq] at hu'S
  obtain ⟨w, hwM₁, hwS, hbw⟩ := mem_subImg.mp hu'S
  obtain ⟨v', hv'⟩ : ∃ v' : ↥(M₁ ⊓ M₂), v' = ⟨w, hSbH hwS⟩ := ⟨_, rfl⟩
  have hv'w : (v' : E) = w := by rw [hv']
  have hbv' : bM β ε v' = u' := by
    rw [hv', burnsideF4ja_bM_eq]
    exact hbw
  have hv'S : (v' : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by rw [hv'w]; exact hwS
  have hv'1 : v' ≠ 1 := by
    intro h
    apply hu1
    have h1 : u' = 1 := by rw [← hbv', h, map_one]
    calc u = x * u' * x⁻¹ := by rw [hu']; group
      _ = 1 := by rw [h1]; group
  have hv'2 : v' * v' = 1 := by
    apply hbM
    rw [map_mul, hbv', map_one, hu']
    calc x⁻¹ * u * x * (x⁻¹ * u * x) = x⁻¹ * (u * u) * x := by group
      _ = 1 := by rw [hu2]; group
  have hconj : IsConj (bM β ε v) (bM β ε v') := by
    rw [isConj_iff, hu, hbv', hu']
    exact ⟨x⁻¹, by rw [inv_inv]⟩
  obtain ⟨g, hgGp, hgv⟩ :=
    (h35 κ f E Gp M₁ M₂ Y β M ε z hyp v v' hvS hv'S hv1 hv'1 hv2 hv'2).mpr hconj
  have hconjC : conjSub g (Gp ⊓ Subgroup.centralizer ({(v : E)} : Set E)) =
      Gp ⊓ Subgroup.centralizer ({w} : Set E) := by
    rw [conjSub_inf, burnsideF4ja_conjSub_of_mem hgGp, ← burnsideF4d_Z1_centralizer_conj, hgv,
      hv'w]
  have hA' : ChF.IsSylowOf 2 (conjSub g (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓
      Subgroup.centralizer ({(v : E)} : Set E))) (Gp ⊓ Subgroup.centralizer ({w} : Set E)) := by
    rw [← hconjC]
    exact F7.isSylowTwoOf_conj hsyl g
  have hle1 : Nat.card ↥(pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({w} : Set E)) ≤
      Nat.card ↥(pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({(v : E)} : Set E)) := by
    have h1 := burnsideF4ja_card_le_of_isSylowOf hA' (inf_le_inf_right _ hSbGp)
      (hSbP.to_le inf_le_left)
    rwa [burnsideF4ja_card_conjSub] at h1
  have hCSv : SinM Gp β ε ⊓ Subgroup.centralizer ({bM β ε v} : Set M) =
      subImg (burnsideF4d_bOne β ε)
        (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({(v : E)} : Set E)) := by
    rw [hSeq, burnsideF4ja_bM_eq]
    exact burnsideF4ja_subImg_inf_centralizer hb₁ _ v.2.1
  have hCSv' : SinM Gp β ε ⊓ Subgroup.centralizer ({u'} : Set M) =
      subImg (burnsideF4d_bOne β ε)
        (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({w} : Set E)) := by
    rw [hSeq, ← hbw]
    exact burnsideF4ja_subImg_inf_centralizer hb₁ _ hwM₁
  have hM₁ : ∀ X : Subgroup E, pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ X ≤ M₁ := fun X =>
    inf_le_left.trans (hSbH.trans inf_le_left)
  have hle2 : Nat.card ↥P ≤ Nat.card ↥(SinM Gp β ε ⊓ Subgroup.centralizer ({u'} : Set M)) := by
    rw [← burnsideF4ja_card_conjSub x⁻¹ P]
    exact Subgroup.card_le_of_le hP'S
  rw [hCSv', L3.card_subImg _ hb₁ (hM₁ _)] at hle2
  have hfinal : Nat.card ↥P ≤
      Nat.card ↥(SinM Gp β ε ⊓ Subgroup.centralizer ({bM β ε v} : Set M)) := by
    rw [hCSv, L3.card_subImg _ hb₁ (hM₁ _)]
    exact hle2.trans hle1
  rw [hu] at hfinal ⊢
  exact burnsideF4ja_isSylowOf_of_card_le hP inf_le_right (hS.2.1.to_le inf_le_left) hfinal

theorem burnsideF4ja_F_4_44_of
    (h24 : F_4_24) (h38 : F_4_38) (h43 : F_4_43) : F_4_44_partial := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL hκ
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  have hME : Nat.card M = Nat.card E := h43 κ f E Gp M₁ M₂ Y β M ε z hyp hL hκ
  haveI : Finite β.G0 := Finite.of_injective _ hyp.inj
  have hle : Nat.card β.G0 ≤ Nat.card E := hME ▸ Nat.card_le_card_of_injective _ hyp.inj
  obtain ⟨hcard, Ġ, _, ⟨Gq, hGq⟩, ⟨e⟩⟩ :=
    h24 κ 2 f E Gp M₁ M₂ hyp.amalgam Y β hyp.faithful inferInstance hle
  have hbij : Function.Bijective (epsG β ε) :=
    (Nat.bijective_iff_injective_and_card _).mpr ⟨hyp.inj, hcard.trans hME.symm⟩
  refine ⟨Ġ, inferInstance, Gq, hGq, ?_, ⟨(MulEquiv.ofBijective (epsG β ε) hbij).symm.trans e⟩⟩
  obtain ⟨T, hT⟩ := burnsideF4ja_exists_isSylowOf (MiOne β ε ⊓ MiTwo β ε)
  have hodd : Odd Gp.index := (h38 κ f E Gp M₁ M₂ Y β M ε z hyp hL T hT).2.2
  have hGqGp : Nat.card Gq = Nat.card Gp :=
    ChF.burnsideF4a_isGenLie_card_eq hGq.1 hyp.amalgam.model
  have hĠ : Nat.card Ġ = Nat.card E := (Nat.card_congr e.toEquiv).symm.trans hcard
  have h1 := Gq.card_mul_index
  have h2 := Gp.card_mul_index
  have hidx : Gq.index = Gp.index := by
    rw [hGqGp, hĠ, ← h2] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  rw [hidx]
  exact hodd

end CFSG.ASVolI
