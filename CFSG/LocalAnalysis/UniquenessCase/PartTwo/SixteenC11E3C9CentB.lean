module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C9Cent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C9Seven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private lemma s1611e3_c9centb_frame_commutator_prod {Z S : Type*} [CommGroup Z] [Group S]
    (hperf : Group.IsPerfect S) :
    commutator (Z × S × S) =
      (⊥ : Subgroup Z).prod ((⊤ : Subgroup S).prod (⊤ : Subgroup S)) := by
  rw [_root_.commutator_def]
  simp only [← Subgroup.top_prod_top]
  rw [Subgroup.commutator_prod_prod, Subgroup.commutator_prod_prod]
  simp only [show ⁅(⊤ : Subgroup Z), ⊤⁆ = ⊥ from commutator_eq_bot Z,
    show ⁅(⊤ : Subgroup S), ⊤⁆ = ⊤ from hperf.commutator_eq_top]

private lemma s1611e3_c9centb_ker_fst_comp_eq_commutator {A S : Type*} [Group A] [Group S]
    (hperf : Group.IsPerfect S) {F : Subgroup A}
    (e : ↥F ≃* Multiplicative (ZMod 7) × S × S) :
    ((MonoidHom.fst (Multiplicative (ZMod 7)) (S × S)).comp e.toMonoidHom).ker =
      commutator ↥F := by
  have hcomm : (commutator ↥F).map e.toMonoidHom =
      (⊥ : Subgroup (Multiplicative (ZMod 7))).prod
        ((⊤ : Subgroup S).prod (⊤ : Subgroup S)) := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
    exact s1611e3_c9centb_frame_commutator_prod hperf
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : e x ∈ (commutator ↥F).map e.toMonoidHom := by
      rw [hcomm]
      simpa [Subgroup.mem_prod] using hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
    rwa [e.injective hyx] at hy
  · intro x hx
    have hx' : e x ∈ (commutator ↥F).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hx
    rw [hcomm] at hx'
    rw [MonoidHom.mem_ker]
    simpa [Subgroup.mem_prod] using hx'

private lemma s1611e3_c9centb_le_of_isPGroup_of_index_not_dvd {X : Type*} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] {A F P : Subgroup X} (hF : F ≤ A)
    (hFn : (F.subgroupOf A).Normal) (hPA : P ≤ A) (hP : IsPGroup p P)
    (hidx : ¬ p ∣ (F.subgroupOf A).index) : P ≤ F := by
  haveI := hFn
  let q : ↥A →* ↥A ⧸ F.subgroupOf A := QuotientGroup.mk' (F.subgroupOf A)
  have hQp : IsPGroup p ((P.subgroupOf A).map q) := hP.comap_subtype.map q
  have hQdvd : Nat.card ((P.subgroupOf A).map q) ∣ (F.subgroupOf A).index := by
    rw [Subgroup.index_eq_card]
    exact Subgroup.card_subgroup_dvd_card _
  have hQ1 : Nat.card ((P.subgroupOf A).map q) = 1 := by
    by_contra hne
    have hpdvd : p ∣ Nat.card ((P.subgroupOf A).map q) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hQp
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hne (by rw [hk, pow_zero])
      rw [hk]
      exact dvd_pow_self p hk0
    exact hidx (hpdvd.trans hQdvd)
  have hQsub : Subsingleton ↥((P.subgroupOf A).map q) :=
    (Nat.card_eq_one_iff_unique.mp hQ1).1
  have hle : P.subgroupOf A ≤ q.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hmem : q x ∈ (P.subgroupOf A).map q := Subgroup.mem_map_of_mem q hx
    have h1 : (⟨q x, hmem⟩ : ↥((P.subgroupOf A).map q)) = 1 := Subsingleton.elim _ _
    simpa using congrArg Subtype.val h1
  have hkerq : q.ker = F.subgroupOf A := QuotientGroup.ker_mk' _
  rw [hkerq] at hle
  intro x hx
  have hx' : (⟨x, hPA hx⟩ : ↥A) ∈ P.subgroupOf A := by
    rw [Subgroup.mem_subgroupOf]
    exact hx
  exact Subgroup.mem_subgroupOf.mp (hle hx')

theorem s1611e3_case9_cent_seven {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h9 : Case168_9 D V₀ V hV L) :
    padicValNat 7 (Nat.card ↥(Mbar D.M V₀ V hV ⊓
      centSub (fixV (barSub V₀ V hV D.T)))) ≤ 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  set Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV with hMb
  set Tb : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV D.T with hTb
  set C : Subgroup (MulAut (Vtil V₀ V hV)) := Mb ⊓ centSub (fixV Tb) with hC
  have hTb2 : IsPGroup 2 Tb := by
    rw [hTb]
    exact D.sylowM.isPGroup.comap_subtype.map (actTil V₀ V hV)
  have hsq : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 18 :=
    s16t_case9_rk_top D h.h1217 hV hc.setting.hyp151 (s1611e3_nine_v1Sub h9) hc.ne_bot
      h9.2.2.1 h9.2.2.2.1
  have htop : (⊤ : Subgroup (Vtil V₀ V hV)) ≠ ⊥ := by
    intro hbot
    have h1 : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = rk ↥(⊥ : Subgroup (Vtil V₀ V hV)) :=
      congrArg (fun H : Subgroup (Vtil V₀ V hV) => rk ↥H) hbot
    rw [rk_bot] at h1
    omega
  obtain ⟨v, -, hv1, hvT⟩ :=
    s15_Lin_exists_ne_one_mem_fixV hTb2 hsq htop (fun _ _ _ _ => Subgroup.mem_top _)
  obtain ⟨P⟩ := Sylow.nonempty (p := 7) (G := ↥C)
  let Pm : Subgroup (MulAut (Vtil V₀ V hV)) := (P : Subgroup ↥C).map C.subtype
  have hPmC : Pm ≤ C := Subgroup.map_subtype_le _
  have hPmMb : Pm ≤ Mb := hPmC.trans inf_le_left
  have hPm7 : IsPGroup 7 Pm := P.isPGroup'.map C.subtype
  obtain ⟨e⟩ := h9.1
  have hL3 : IsL3 ↥(lBar V₀ V hV L) 1 := h9.2.1
  have hperf : Group.IsPerfect ↥(lBar V₀ V hV L) :=
    s16c167_isPSL_isPerfect (s16c167_isPSL_of_isL3 hL3)
  let F : Subgroup (MulAut (Vtil V₀ V hV)) := Fstar Mb
  let eF : ↥F ≃* Multiplicative (ZMod 7) × ↥(lBar V₀ V hV L) × ↥(lBar V₀ V hV L) := e
  let E : Subgroup (MulAut (Vtil V₀ V hV)) := (commutator ↥F).map F.subtype
  have hFM : F ≤ Mb := (s16c167_cfg10_fstar_facts Mb).1
  have hMb7 : padicValNat 7 (Nat.card Mb) = 3 := (s1611e3_case9_mbar_seven h9).1
  have hF7 : padicValNat 7 (Nat.card F) = 3 := by
    have e' : ↥(⊤ : Subgroup ↥F) ≃*
        Multiplicative (ZMod 7) × ↥(lBar V₀ V hV L) × ↥(lBar V₀ V hV L) :=
      Subgroup.topEquiv.trans eF
    exact (s1611e3_c9_seven_count (A := ↥F) (F := ⊤) (hF := le_top) hL3 e').1
  have hnormF : (F.subgroupOf Mb).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFM).2 fun x hx => by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy; exact (s16c167_cfg10_fstar_facts Mb).2.1 x hx y hy
      · intro hy
        have h' := (s16c167_cfg10_fstar_facts Mb).2.1 x⁻¹ (Mb.inv_mem hx) (x * y * x⁻¹) hy
        rwa [show x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y by group] at h'
  have hidx : ¬ 7 ∣ (F.subgroupOf Mb).index := by
    have hcardF : Nat.card ↥(F.subgroupOf Mb) = Nat.card F := by
      rw [← Subgroup.card_map_of_injective Mb.subtype_injective, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hFM]
    have hidxne : (F.subgroupOf Mb).index ≠ 0 := by
      intro h0
      have hprod := Subgroup.card_mul_index (H := F.subgroupOf Mb)
      rw [h0, mul_zero] at hprod
      exact Nat.card_pos.ne' hprod.symm
    have hprod := Subgroup.card_mul_index (H := F.subgroupOf Mb)
    rw [hcardF] at hprod
    have hmul := padicValNat.mul (p := 7) (Nat.card_pos (α := ↥F)).ne' hidxne
    rw [hprod, hMb7, hF7] at hmul
    have hzero : padicValNat 7 (F.subgroupOf Mb).index = 0 := by omega
    intro h7dvd
    exact ((dvd_iff_padicValNat_ne_zero (p := 7) hidxne).mp h7dvd) hzero
  have hPF : Pm ≤ F :=
    s1611e3_c9centb_le_of_isPGroup_of_index_not_dvd hFM hnormF hPmMb hPm7 hidx
  have hPmE : Pm ⊓ E = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxP, hxE⟩ := hx
    have hxMb : x ∈ Mb := hPmMb hxP
    have hxcent : x ∈ centSub (fixV Tb) := (hPmC hxP).2
    have hxv : x v = v := (mem_centSub.mp hxcent) v hvT
    have hx7 : x ^ 7 = 1 := by
      obtain ⟨y, hyP, hyx⟩ := Subgroup.mem_map.mp hxP
      obtain ⟨k, hk⟩ := (isPGroup_iff_orderOf_dvd_pow.mp P.isPGroup') ⟨y, hyP⟩
      have hk'' : (⟨y, hyP⟩ : ↥(P : Subgroup ↥C)) ^ 7 ^ k = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp hk
      have hk' : y ^ 7 ^ k = 1 := by
        simpa using congrArg Subtype.val hk''
      have hxk : x ^ 7 ^ k = 1 := by
        rw [← hyx, ← map_pow, hk', map_one]
      exact (s1611e3_case9_mbar_seven h9).2 x hxMb ⟨k, hxk⟩
    exact s1611e3_case9_E_fixed h hc h9 hxE hx7 hv1 hvT hxv
  set ψ : ↥F →* Multiplicative (ZMod 7) :=
    (MonoidHom.fst (Multiplicative (ZMod 7))
      (↥(lBar V₀ V hV L) × ↥(lBar V₀ V hV L))).comp eF.toMonoidHom with hψ
  have hEsub : E.subgroupOf F = commutator ↥F :=
    Subgroup.comap_map_eq_self_of_injective F.subtype_injective (commutator ↥F)
  have hker : ψ.ker = E.subgroupOf F := by
    rw [hψ, s1611e3_c9centb_ker_fst_comp_eq_commutator hperf eF, hEsub]
  let PC : Subgroup ↥F := Pm.subgroupOf F
  have hPCcard : Nat.card PC = Nat.card Pm := by
    have h1 : PC.map F.subtype = Pm := by
      rw [show PC = Pm.subgroupOf F from rfl, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hPF]
    rw [← Subgroup.card_map_of_injective F.subtype_injective (K := PC), h1]
  have h4 : PC ⊓ E.subgroupOf F = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxPC, hxE⟩ := hx
    have h1 : (x : MulAut (Vtil V₀ V hV)) ∈ Pm :=
      Subgroup.mem_subgroupOf.mp (by rwa [show PC = Pm.subgroupOf F from rfl] at hxPC)
    have h2 : (x : MulAut (Vtil V₀ V hV)) ∈ E := Subgroup.mem_subgroupOf.mp hxE
    have h3 : (x : MulAut (Vtil V₀ V hV)) ∈ Pm ⊓ E := ⟨h1, h2⟩
    rw [hPmE, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have hinj : Function.Injective (fun x : ↥PC => ψ (x : ↥F)) := by
    intro x y hxy
    have hxy' : ψ (x : ↥F) = ψ (y : ↥F) := hxy
    have h1 : (x : ↥F) * (y : ↥F)⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy', mul_inv_cancel]
    have h2 : (x : ↥F) * (y : ↥F)⁻¹ ∈ PC := PC.mul_mem x.2 (PC.inv_mem y.2)
    have h3 : (x : ↥F) * (y : ↥F)⁻¹ ∈ (⊥ : Subgroup ↥F) := by
      rw [← h4]
      exact ⟨h2, by rwa [hker] at h1⟩
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h3
    exact Subtype.ext h3
  have hcardPC : Nat.card PC ≤ 7 := by
    have hle := Nat.card_le_card_of_injective (f := fun x : ↥PC => ψ (x : ↥F)) hinj
    have h7 : Nat.card (Multiplicative (ZMod 7)) = 7 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    rwa [h7] at hle
  have hcardPm : Nat.card Pm ≤ 7 := by
    rw [← hPCcard]
    exact hcardPC
  have hcardP : Nat.card (P : Subgroup ↥C) = Nat.card Pm :=
    (Subgroup.card_map_of_injective (K := (P : Subgroup ↥C)) C.subtype_injective).symm
  have h7pow : Nat.card (P : Subgroup ↥C) = 7 ^ padicValNat 7 (Nat.card C) := by
    rw [Sylow.card_eq_multiplicity P, Nat.factorization_def _ (Fact.out : Nat.Prime 7)]
  have hk : padicValNat 7 (Nat.card C) ≤ 1 := by
    have h1 : 7 ^ padicValNat 7 (Nat.card C) ≤ 7 ^ 1 := by
      rw [pow_one, ← h7pow, hcardP]
      exact hcardPm
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 7)).1 h1
  exact hk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
