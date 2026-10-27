module

public import CFSG.Quasithin.H13.GoldschmidtCTKSet
public import CFSG.Quasithin.H13.GoldschmidtCTKY
public import CFSG.Quasithin.H13.A5Sit15d

public section

namespace CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.CTK
open scoped commutatorElement Pointwise

@[expose] def stab5A6 : Subgroup (Perm (Fin 6)) where
  carrier := {σ | σ 5 = 5 ∧ Perm.sign σ = 1}
  mul_mem' := fun {a b} ha hb =>
    ⟨by rw [Perm.mul_apply, hb.1, ha.1], by rw [Perm.sign_mul, ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨rfl, Perm.sign_one⟩
  inv_mem' := fun {a} ha => ⟨Perm.inv_eq_iff_eq.2 ha.1.symm, by rw [Perm.sign_inv, ha.2]⟩

theorem mem_stab5A6 {σ : Perm (Fin 6)} : σ ∈ stab5A6 ↔ σ 5 = 5 ∧ Perm.sign σ = 1 := Iff.rfl

theorem card_stab5A6 : Nat.card stab5A6 = 60 := by
  have : Fintype.card {σ : Perm (Fin 6) // σ 5 = 5 ∧ Perm.sign σ = 1} = 60 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem ctk_card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem ctk_card_ker_mul_card_range {H H' : Type} [Group H] [Group H'] [Finite H] (φ : H →* H') :
    Nat.card φ.ker * Nat.card φ.range = Nat.card H := by
  have h1 := Subgroup.card_mul_index φ.ker
  rwa [Subgroup.index_ker] at h1

theorem Setting4.exists_rho_of_alt5 (S : Setting4 G T L V)
    {K : Subgroup G} (hKL : K ≤ L ⊓ S.fix5V) (hshort : IsShort2 K) (halt : IsAltType K 5)
    (hO2 : pCoreOf 2 K = V) {σ : Perm (Fin 6)} (h5 : σ 5 = 5) (hs : Perm.sign σ = 1) :
    ∃ k : ↥(Subgroup.normalizer (V : Set G)), (k : G) ∈ K ∧ S.frame.ρ k = σ := by
  have hU := blockU_eq_of_alt5 hshort halt hO2 S.card_V
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hKL.trans (inf_le_left.trans S.frame.L_le)
  let ρK : ↥K →* Perm (Fin 6) := S.frame.ρ.comp (Subgroup.inclusion hKN)
  obtain ⟨α, hαs, hαker, -⟩ := halt
  have hpc_le : CFSG.pCore 2 ↥K ≤ ρK.ker := by
    intro k hk
    have hkV : (k : G) ∈ V := by
      rw [← hO2]
      exact ⟨k, hk, rfl⟩
    rw [MonoidHom.mem_ker]
    exact (S.rho_eq_one_iff (Subgroup.inclusion hKN k)).2 (S.V_le_centralizer_V hkV)
  have hker_le : ρK.ker ≤ CFSG.pCore 2 ↥K := by
    rw [← hαker]
    intro k hk
    by_contra hnk
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    have hnorm : ((ρK.ker).map α).Normal := Subgroup.Normal.map inferInstance α hαs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((ρK.ker).map α) with hb | ht
    · apply hnk
      have := Subgroup.mem_map_of_mem α hk
      rw [hb, Subgroup.mem_bot] at this
      exact this
    · have hall : ∀ g : ↥K, g ∈ ρK.ker := by
        intro g
        have hg : α g ∈ (ρK.ker).map α := by rw [ht]; exact Subgroup.mem_top _
        obtain ⟨n, hn, hng⟩ := hg
        have h1 : g * n⁻¹ ∈ α.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, ← hng, mul_inv_cancel]
        have h2 : g * n⁻¹ ∈ ρK.ker := hpc_le (hαker ▸ h1)
        have := ρK.ker.mul_mem h2 hn
        simpa using this
      have hKC : K ≤ Subgroup.centralizer (V : Set G) := fun k hk =>
        (S.rho_eq_one_iff ⟨k, hKN hk⟩).1 (hall ⟨k, hk⟩)
      have hVbot : V = ⊥ := by
        rw [← hU]
        unfold blockU blockQ
        rw [hO2]
        refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun v hv => ?_
        refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
        exact (Subgroup.mem_centralizer_iff.mp (hKC hk) v hv).symm
      have := S.card_V
      rw [hVbot, Subgroup.card_bot] at this
      omega
  have hker_eq : ρK.ker = α.ker := by
    rw [hαker]
    exact le_antisymm hker_le hpc_le
  have h1 := ctk_card_ker_mul_card_range ρK
  have h2 := ctk_card_ker_mul_card_range α
  have hrange : Nat.card α.range = 60 := by
    rw [MonoidHom.range_eq_top.2 hαs, Subgroup.card_top]
    exact ctk_card_alt5
  rw [hker_eq] at h1
  rw [hrange] at h2
  have hpos : 0 < Nat.card α.ker := Nat.card_pos
  have hr : Nat.card ρK.range = 60 := Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  have hle : ρK.range ≤ stab5A6 := by
    rintro _ ⟨k, rfl⟩
    refine ⟨(S.mem_fix5V.1 (hKL k.2).2).2, ?_⟩
    exact Perm.mem_alternatingGroup.1 ((S.frame.image_L _).1 ⟨Subgroup.inclusion hKN k,
      (hKL k.2).1, rfl⟩)
  have heq : ρK.range = stab5A6 :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_stab5A6, hr])
  have hσ : σ ∈ ρK.range := heq ▸ (mem_stab5A6.2 ⟨h5, hs⟩)
  obtain ⟨k, hk⟩ := hσ
  exact ⟨Subgroup.inclusion hKN k, k.2, hk⟩

theorem Setting4.eq_L5 (S : Setting4 G T L V) (hhat : ¬ IsHatA6 L)
    {K : Subgroup G} (hKL : K ≤ L ⊓ S.fix5V) (hshort : IsShort2 K) (halt : IsAltType K 5)
    (hO2 : pCoreOf 2 K = V) (hKeq : oTwoRes (pCoreOf 2 (L ⊔ T) ⊔ K) = K) : K = S.L5 := by
  have e : oTwoRes K = K := by
    have h1 := oTwoRes_oTwoRes (pCoreOf 2 (L ⊔ T) ⊔ K)
    rw [hKeq] at h1
    exact h1
  apply le_antisymm
  · calc K = oTwoRes K := e.symm
      _ ≤ oTwoRes (L ⊓ S.fix5V) := Subgroup.closure_mono fun y hy => ⟨hKL hy.1, hy.2⟩
  · calc S.L5 = oTwoRes (L ⊓ S.fix5V) := rfl
      _ ≤ oTwoRes (pCoreOf 2 (L ⊔ T) ⊔ K) := by
        refine Subgroup.closure_mono fun y hy => ⟨?_, hy.2⟩
        obtain ⟨hyL, hy5⟩ := hy.1
        obtain ⟨hyN, hy5'⟩ := S.mem_fix5V.1 hy5
        have hsy : Perm.sign (S.frame.ρ ⟨y, hyN⟩) = 1 :=
          Perm.mem_alternatingGroup.1 ((S.frame.image_L _).1 ⟨_, hyL, rfl⟩)
        obtain ⟨k, hkK, hρk⟩ := S.exists_rho_of_alt5 hKL hshort halt hO2 hy5' hsy
        have hrN : (k : G)⁻¹ * y ∈ Subgroup.normalizer (V : Set G) :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ k.2) hyN
        have hr1 : S.frame.ρ ⟨(k : G)⁻¹ * y, hrN⟩ = 1 := by
          have e : (⟨(k : G)⁻¹ * y, hrN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
              k⁻¹ * ⟨y, hyN⟩ := rfl
          rw [e, map_mul, map_inv, hρk, inv_mul_cancel]
        have hrQ : (k : G)⁻¹ * y ∈ pCoreOf 2 (L ⊔ T) :=
          S.R_le_Q hhat ⟨L.mul_mem (L.inv_mem (hKL hkK).1) hyL,
            (S.rho_eq_one_iff _).1 hr1⟩
        have hye : y = (k : G) * ((k : G)⁻¹ * y) := by group
        rw [hye]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hkK) (Subgroup.mem_sup_left hrQ)
      _ = K := hKeq

@[expose] noncomputable def Setting4.fixV (S : Setting4 G T L V) (ω : Fin 6) : Subgroup G :=
  ((MulAction.stabilizer (Perm (Fin 6)) ω).comap S.frame.ρ).map
    (Subgroup.normalizer (V : Set G)).subtype

theorem Setting4.mem_fixV (S : Setting4 G T L V) {ω : Fin 6} {x : G} :
    x ∈ S.fixV ω ↔ ∃ hx : x ∈ Subgroup.normalizer (V : Set G), S.frame.ρ ⟨x, hx⟩ ω = ω := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem Setting4.KH_le_fixV (S : Setting4 G T L V)
    (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hn : H ≤ Subgroup.normalizer (S.L1 : Set G))
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) {l : ↥(Subgroup.normalizer (V : Set G))}
    {ω : Fin 6} (hω : ω = 4 ∨ ω = 5) (hl : S.frame.ρ l ω = ω) : S.KH H l ≤ S.fixV ω := by
  obtain ⟨hK4, -⟩ := S.lemma13_5_14_two hNS h1356two h13315 hH
    (S.UH_le_L1_six hNS h13315 h1356two hH hn hna) hna
  have hK4' : ∀ τ ∈ K4L, τ ω = ω := by
    rcases hω with rfl | rfl <;> decide +kernel
  refine sup_le (fun u hu => S.mem_fixV.2 ⟨_, hK4' _ (hK4 u hu)⟩) ?_
  rintro _ ⟨u, hu, rfl⟩
  have hu' := hK4 u hu
  have huN : u ∈ Subgroup.normalizer (V : Set G) :=
    S.frame.L_le (S.L1_le.trans inf_le_left (S.UH_le_L1_six hNS h13315 h1356two hH hn hna hu))
  have hmem : (l : G)⁻¹ * u * l ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ l.2) huN) l.2
  show (MulAut.conj (l : G)⁻¹) u ∈ S.fixV ω
  rw [MulAut.conj_apply, inv_inv]
  refine S.mem_fixV.2 ⟨hmem, ?_⟩
  have e : (⟨(l : G)⁻¹ * u * l, hmem⟩ : ↥(Subgroup.normalizer (V : Set G))) =
      l⁻¹ * ⟨u, huN⟩ * l := rfl
  rw [e, map_mul, map_mul, map_inv, Perm.mul_apply, Perm.mul_apply, hl,
    hK4' _ hu']
  exact Perm.inv_eq_iff_eq.2 hl.symm

theorem Setting4.fixV_five_le (S : Setting4 G T L V) : S.fixV 5 ≤ S.fix5V := fun _ hx =>
  S.mem_fix5V.2 (S.mem_fixV.1 hx)

theorem input13515CTK_of (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (hobl : Obl13_5_14Six) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h36 : Vol2Native.A36CoreForSQTKCat) (hl2 : L2MultiplierFact)
    (hlist : ∀ (X : Type) [Group X] [Finite X], CFSG.SectionRank.IsSQTKCat X →
      ∀ (H : Subgroup X) (N : Subgroup ↥H) [N.Normal] [IsSimpleGroup (↥H ⧸ N)],
        (∃ a b : ↥H ⧸ N, a * b ≠ b * a) → CFSG.Milestones.SQTKSimpleList (↥H ⧸ N))
    (hExcl : ExclA5Block) : Input13515CTK := by
  intro G _ _ T L V S H l hNS hH hn hna hhat hl hlL hlT hρ
  have hsimple := S.h13.simple
  have hLS : LocalSQTK G := (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  obtain ⟨hKeq, hshort, halt, hO2, hU, hQ8⟩ :=
    hobl G T L V S H l hNS hH hn hna hhat hl hlL hlT hρ
  obtain ⟨P⟩ : Nonempty (A5SitPf15 (S.toA5Sit hNS h13315 h1356two hH hna)
      (S.toA5SitY hNS h13315 h1356two hH hna hhat)) :=
    (S.toA5Sit hNS h13315 h1356two hH hna).nonempty_pf15 VolI.stmtF956i _ hn hU hQ8
  have hcTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    P.centralizer_T_L S.uniqueM S.V_le_pCoreOf_M
  obtain ⟨y, hyI, hy3, hyN⟩ := P.S3_facts.2.2.2
  have hUH : conjClosure S.V3 H ≤ S.L5 :=
    (S.UH_le_L1_six hNS h13315 h1356two hH hn hna).trans S.L1_le_L5
  have hyD : ∀ d ∈ S.CD, y * d * y⁻¹ = d := fun d hd =>
    P.commute_y hyI hy3 hd.1 fun u hu =>
      (Subgroup.mem_centralizer_iff.mp hd.2 u (hUH hu)).symm
  have hmain : IsShort2 S.L5 → IsAltType S.L5 5 → pCoreOf 2 S.L5 = V → S.CD = ⊥ :=
    fun hs ha ho => (CTKHyp.mk hhat hs ha ho hcTL).CD_eq_bot hLS h37 h38 h39 h36 hl2 hlist
      hExcl ⟨y, hy3, hyN, hyD⟩
  have hKL : S.KH H l ≤ L := S.KH_le_L hNS h13315 h1356two hH hn hna (l := ⟨l, hl⟩) hlL
  have hKeq : oTwoRes (pCoreOf 2 (L ⊔ T) ⊔ S.KH H l) = S.KH H l := hKeq
  have hshort : IsShort2 (S.KH H l) := hshort
  have halt : IsAltType (S.KH H l) 5 := halt
  have hO2 : pCoreOf 2 (S.KH H l) = V := hO2
  show T ⊓ Subgroup.centralizer (S.KH H l : Set G) = ⊥
  rcases hρ with h4 | h5
  ·
    obtain ⟨t, htT, hρt⟩ :=
      S.frame.DA_T _ s0145_facts.1 (Perm.mem_alternatingGroup.2 s0145_facts.2.1)
    have htNV : (t : G) ∈ Subgroup.normalizer (V : Set G) := t.2
    have htL : (t : G) ∈ Subgroup.normalizer (L : Set G) := S.T_le_NL htT
    have hK4 : S.KH H l ≤ S.fixV 4 :=
      S.KH_le_fixV hNS h13315 h1356two hH hn hna (l := ⟨l, hl⟩) (ω := 4) (Or.inl rfl) h4
    have hQ : (t : G) ∈ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
      le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_right htT)
    set K' : Subgroup G := (S.KH H l).map (MulAut.conj (t : G)).toMonoidHom with hK'
    have hK'fix : K' ≤ L ⊓ S.fix5V := by
      rintro _ ⟨k, hk, rfl⟩
      refine ⟨?_, S.mem_fix5V.2 ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp htL k).mp (hKL hk)
      · obtain ⟨hkN, hk4⟩ := S.mem_fixV.1 (hK4 hk)
        have hmem : (t : G) * k * (t : G)⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ htNV hkN) (Subgroup.inv_mem _ htNV)
        refine ⟨hmem, ?_⟩
        have e : (⟨(t : G) * k * (t : G)⁻¹, hmem⟩ : ↥(Subgroup.normalizer (V : Set G))) =
            t * ⟨k, hkN⟩ * t⁻¹ := rfl
        obtain ⟨hs4, hs5⟩ := s0145_apply
        show (S.frame.ρ ⟨(t : G) * k * (t : G)⁻¹, hmem⟩) 5 = 5
        rw [e, map_mul, map_mul, map_inv, hρt, Perm.mul_apply, Perm.mul_apply, hs5, hk4, hs4]
    have hshort' : IsShort2 K' := (Lin2.isShort2_map_equiv_iff (MulAut.conj (t : G)) _).2 hshort
    have halt' : IsAltType K' 5 := L238.IsAltType.map_equiv halt (MulAut.conj (t : G))
    have hO2' : pCoreOf 2 K' = V := by
      rw [hK', pCoreOf_map_equiv 2 (MulAut.conj (t : G)), hO2]
      exact CTK.map_conj_eq_of_mem_normalizer htNV
    have hKeq' : oTwoRes (pCoreOf 2 (L ⊔ T) ⊔ K') = K' := by
      have hmapQ : (pCoreOf 2 (L ⊔ T)).map (MulAut.conj (t : G)).toMonoidHom =
          pCoreOf 2 (L ⊔ T) := CTK.map_conj_eq_of_mem_normalizer hQ
      have h1 : conjSub (t : G) (pCoreOf 2 (L ⊔ T) ⊔ S.KH H l) =
          pCoreOf 2 (L ⊔ T) ⊔ K' := by
        show (pCoreOf 2 (L ⊔ T) ⊔ S.KH H l).map (MulAut.conj (t : G)).toMonoidHom = _
        rw [Subgroup.map_sup, hmapQ]
      rw [← h1, ← conjSub_oTwoRes, hKeq]
      rfl
    have hK'5 : K' = S.L5 := S.eq_L5 hhat hK'fix hshort' halt' hO2' hKeq'
    have hCD := hmain (hK'5 ▸ hshort') (hK'5 ▸ halt') (hK'5 ▸ hO2')
    refine eq_bot_iff.2 fun x hx => ?_
    have hxT : x ∈ T := hx.1
    have hz : (t : G) * x * (t : G)⁻¹ ∈ S.CD := by
      refine ⟨T.mul_mem (T.mul_mem htT hxT) (T.inv_mem htT), Subgroup.mem_centralizer_iff.2 ?_⟩
      intro k' hk'
      rw [← hK'5] at hk'
      obtain ⟨k, hk, rfl⟩ := hk'
      have hxk : k * x = x * k := Subgroup.mem_centralizer_iff.mp hx.2 k hk
      show (t : G) * k * (t : G)⁻¹ * ((t : G) * x * (t : G)⁻¹) =
        (t : G) * x * (t : G)⁻¹ * ((t : G) * k * (t : G)⁻¹)
      calc (t : G) * k * (t : G)⁻¹ * ((t : G) * x * (t : G)⁻¹)
          = (t : G) * (k * x) * (t : G)⁻¹ := by group
        _ = (t : G) * (x * k) * (t : G)⁻¹ := by rw [hxk]
        _ = (t : G) * x * (t : G)⁻¹ * ((t : G) * k * (t : G)⁻¹) := by group
    rw [hCD, Subgroup.mem_bot] at hz
    have : x = 1 := by
      have h2 : (t : G)⁻¹ * ((t : G) * x * (t : G)⁻¹) * (t : G) = x := by group
      rw [hz] at h2
      simpa using h2.symm
    exact (Subgroup.mem_bot).2 this
  · have hK5 : S.KH H l ≤ L ⊓ S.fix5V :=
      le_inf hKL ((S.KH_le_fixV hNS h13315 h1356two hH hn hna (l := ⟨l, hl⟩) (ω := 5)
        (Or.inr rfl) h5).trans S.fixV_five_le)
    have hK5eq : S.KH H l = S.L5 := S.eq_L5 hhat hK5 hshort halt hO2 hKeq
    rw [hK5eq]
    exact hmain (hK5eq ▸ hshort) (hK5eq ▸ halt) (hK5eq ▸ hO2)

end CFSG.Quasithin.H13.A6
