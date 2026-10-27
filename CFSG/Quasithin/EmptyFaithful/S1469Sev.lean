module

public import CFSG.Quasithin.EmptyFaithful.S146R4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
public import CFSG.Quasithin.Background.A1bTransvection
public import CFSG.Quasithin.EmptyFaithful.S146Three

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.conjClosure_le_pCoreOf_mcOf (S : Setting146 G T M) {H : Subgroup G}
    (hH : IsHTM T M H) : conjClosure (VZ T M) H ≤ pCoreOf 2 (mcOf T) :=
  (conjClosure_mono le_rfl (S.le_mcOf hH)).trans (S.conjClosure_le_pCoreOf S.isHTM_mcOf)

theorem Setting146.mem_tU_of_isInvU (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H)
    {u : G} (hu : IsInvU T M H u) : u ∈ tU T u := by
  refine (S146T.mem_tU_iff).mpr ⟨S.pCoreOf_mcOf_le (S.conjClosure_le_pCoreOf_mcOf hH hu.mem), ?_⟩
  simp

theorem Setting146.lemma115Hyp_of_isIStar (S : Setting146 G T M) {H : Subgroup G}
    (hH : IsHTM T M H) {u : G} (hu : IsInvU T M H u) {I : Subgroup G} (hI : IsIStar T M u I)
    (hsyl : IsSylowTwoOf (T ⊓ I) I) {z : G} (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) :
    CFSG.QuasithinUnique.Lemma115Hyp I (T ⊓ I) (mcOf T) z := by
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTG : T ≤ mcOf T := le_centralizer_quasithinOmegaOneCenter T
  have hQ1T : pCoreOf 2 (mcOf T) ≤ T := S.pCoreOf_mcOf_le
  have huT : u ∈ tU T u := S.mem_tU_of_isInvU hH hu
  have huQ : u ∈ pCoreOf 2 (mcOf T) := S.conjClosure_le_pCoreOf_mcOf hH hu.mem
  have huI : u ∈ I := hI.1.1.1 huT
  have hTuI : tU T u ≤ I := hI.1.1.1
  have huO : u ∈ pCoreOf 2 (I ⊓ mcOf T) := by
    have hA : pCoreOf 2 (mcOf T) ⊓ (I ⊓ mcOf T) ≤ pCoreOf 2 (I ⊓ mcOf T) := by
      refine le_pCoreOf_of_le_normalizer inf_le_right ?_
        ((pCoreOf_isPGroup 2 (mcOf T)).to_le inf_le_left)
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hn := Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (mcOf T) hg.2) x
      constructor
      · rintro ⟨hx1, hx2⟩
        exact ⟨hn.mp hx1, (I ⊓ mcOf T).mul_mem ((I ⊓ mcOf T).mul_mem hg hx2)
          ((I ⊓ mcOf T).inv_mem hg)⟩
      · rintro ⟨hx1, hx2⟩
        refine ⟨hn.mpr hx1, ?_⟩
        have := (I ⊓ mcOf T).mul_mem ((I ⊓ mcOf T).mul_mem ((I ⊓ mcOf T).inv_mem hg) hx2) hg
        simpa [mul_assoc] using this
    exact hA ⟨huQ, huI, pCoreOf_le 2 _ huQ⟩
  have hzT : z ∈ T := S146T.Z_le hz
  have hzu : z ∈ tU T u := (S146T.mem_tU_iff).mpr ⟨hzT,
    commutatorElement_eq_one_iff_mul_comm.mpr (S146T.comm_Z_T (hQ1T huQ) hz).symm⟩
  have hzI : z ∈ T ⊓ I := ⟨hzT, hTuI hzu⟩
  refine ⟨hI.1.1.2, hsyl, charTwo_of_inH' S.hyp.qtke S.hyp.sylow hG.1, hG.1.2,
    inf_le_left.trans hTG, ?_, ?_, hz1, hzI,
    Subgroup.mem_centralizer_iff.mpr fun g hg => S146T.comm_Z_T hg.1 hz, S146T.Z_sq hz⟩
  ·
    rintro x ⟨hxQ, hxC⟩
    have hxu : u * x = x * u := Subgroup.mem_centralizer_iff.mp hxC u huO
    have hxT : x ∈ tU T u := (S146T.mem_tU_iff).mpr ⟨hQ1T hxQ,
      commutatorElement_eq_one_iff_mul_comm.mpr hxu.symm⟩
    exact hTuI hxT
  ·
    intro g hg
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    by_cases hx1 : x = 1
    · simp [hx1]
    · have hxz : x = z := S.Z_eq_of_iff hx hz ⟨fun h => absurd h hx1, fun h => absurd h hz1⟩
      subst hxz
      exact Subgroup.mem_centralizer_iff.mp hg x rfl

theorem Setting146.charTwo_inf_mcOf (S : Setting146 G T M) {H : Subgroup G}
    (hH : IsHTM T M H) {u : G} (hu : IsInvU T M H u) {I : Subgroup G} (hI : IsIStar T M u I)
    (hsyl : IsSylowTwoOf (T ⊓ I) I) {z : G} (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) :
    CharTwo (I ⊓ mcOf T) :=
  (S.lemma115Hyp_of_isIStar hH hu hI hsyl hz hz1).charTwo_inf

theorem Setting146.oddCoreIn_eq_bot (S : Setting146 G T M) {H : Subgroup G}
    (hH : IsHTM T M H) {u : G} (hu : IsInvU T M H u) {I : Subgroup G} (hI : IsIStar T M u I)
    (hsyl : IsSylowTwoOf (T ⊓ I) I) {z : G} (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) :
    oddCoreIn I = ⊥ := by
  have h115 := S.lemma115Hyp_of_isIStar hH hu hI hsyl hz hz1
  have hO := h115.oddCoreIn_properties.1
  set O := oddCoreIn I with hOdef
  set V := VZ T M with hV
  set U := conjClosure V H with hU
  have hUab : IsElemAbelian 2 U := S.lemma_14_5_15_two hH
  have hVU : V ≤ U := le_conjClosure _ _
  have hUT : U ≤ T := (S.conjClosure_le_pCoreOf hH).trans (S.pCoreOf_le_T hH)
  have huU : u ∈ U := hu.mem
  have hVI : V ≤ I := fun v hv => hI.1.1.1 <|
    (S146T.mem_tU_iff).mpr ⟨hUT (hVU hv), commutatorElement_eq_one_iff_mul_comm.mpr
      (congrArg Subtype.val (hUab.1.is_comm.comm (⟨v, hVU hv⟩ : U) ⟨u, huU⟩))⟩
  have hVN : V ≤ Subgroup.normalizer (O : Set G) := fun v hv => le_normalizer_oddCoreIn I (hVI hv)
  have hodd : Odd (Nat.card O) := odd_card_oddCoreIn I
  have hpower : ∀ member : V, member ^ 2 = 1 := fun member =>
    Subtype.ext (by simpa using hUab.2 (member : G) (hVU member.2))
  have hcard : Nat.card V = 2 ^ 2 := by rw [hV, S.hyp.rank_two]; norm_num
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two V O hpower hcard hodd.not_two_dvd_nat hVN
  have hVQ1 : V ≤ pCoreOf 2 (mcOf T) :=
    (le_conjClosure V (mcOf T)).trans (S.conjClosure_le_pCoreOf S.isHTM_mcOf)
  have hZV : quasithinOmegaOneCenter T ≤ V := le_conjClosure _ _
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := le_normalizer_conjClosure _ _
  have hLM : yOfL22 T M ≤ M := S.hyp1281.le
  have hterm : ∀ v : V, v ≠ 1 → O ⊓ Subgroup.centralizer ({(v : G)} : Set G) ≤ mcOf T := by
    intro v hv x hx
    have hv1 : (v : G) ≠ 1 := fun h => hv (Subtype.ext h)
    obtain ⟨l, hlL, hl⟩ := S.hyp1281.exists_conj_eq (le_conjClosure _ _ hz) v.2 hz1 hv1
    have hlN : l ∈ Subgroup.normalizer (V : Set G) := hMV (hLM hlL)
    have hxv : (v : G) * x = x * (v : G) := Subgroup.mem_centralizer_iff.mp hx.2 v rfl
    have hxG : l⁻¹ * x * l ∈ mcOf T := by
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      by_cases hy1 : y = 1
      · simp [hy1]
      · have hyz : y = z := S.Z_eq_of_iff hy hz ⟨fun h => absurd h hy1, fun h => absurd h hz1⟩
        subst hyz
        have h1 : l * y * l⁻¹ * x = x * (l * y * l⁻¹) := by rw [hl]; exact hxv
        calc y * (l⁻¹ * x * l) = l⁻¹ * (l * y * l⁻¹ * x) * l := by group
          _ = l⁻¹ * (x * (l * y * l⁻¹)) * l := by rw [h1]
          _ = (l⁻¹ * x * l) * y := by group
    have hQ : ∀ y : G, l⁻¹ * y * l ∈ pCoreOf 2 (mcOf T) →
        l⁻¹ * (x * y * x⁻¹) * l ∈ pCoreOf 2 (mcOf T) := by
      intro y hy
      have hn := Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 (mcOf T) hxG) (l⁻¹ * y * l)
      have e : l⁻¹ * (x * y * x⁻¹) * l = (l⁻¹ * x * l) * (l⁻¹ * y * l) * (l⁻¹ * x * l)⁻¹ := by
        group
      rw [e]
      exact hn.mp hy
    have hxV : x ∈ Subgroup.centralizer (V : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      set c : G := x * w * x⁻¹ * w⁻¹ with hc
      have hcO : c ∈ O := by
        have h1 : w * x⁻¹ * w⁻¹ ∈ O := by
          have := (Subgroup.mem_normalizer_iff.mp (hVN hw) x⁻¹).mp (O.inv_mem hx.1)
          simpa [mul_assoc] using this
        have : c = x * (w * x⁻¹ * w⁻¹) := by rw [hc]; group
        rw [this]; exact O.mul_mem hx.1 h1
      have hwQ : l⁻¹ * w * l ∈ pCoreOf 2 (mcOf T) := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlN) w).mp hw
        simpa using hVQ1 this
      have hcQ : l⁻¹ * c * l ∈ pCoreOf 2 (mcOf T) := by
        have e : l⁻¹ * c * l = (l⁻¹ * (x * w * x⁻¹) * l) * (l⁻¹ * w * l)⁻¹ := by rw [hc]; group
        rw [e]
        exact (pCoreOf 2 (mcOf T)).mul_mem (hQ w hwQ) ((pCoreOf 2 (mcOf T)).inv_mem hwQ)
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (pCoreOf_isPGroup 2 (mcOf T)))
        (⟨l⁻¹ * c * l, hcQ⟩ : pCoreOf 2 (mcOf T))
      have hck : c ^ (2 ^ k) = 1 := by
        have h1 : (l⁻¹ * c * l) ^ (2 ^ k) = 1 := by
          have := pow_orderOf_eq_one (⟨l⁻¹ * c * l, hcQ⟩ : pCoreOf 2 (mcOf T))
          rw [hk] at this
          exact congrArg Subtype.val this
        have e : (l⁻¹ * c * l) ^ (2 ^ k) = l⁻¹ * c ^ (2 ^ k) * l := by
          have := conj_pow (a := l⁻¹) (b := c) (i := 2 ^ k)
          simpa using this
        rw [e] at h1
        have : c ^ (2 ^ k) = 1 := by
          calc c ^ (2 ^ k) = l * (l⁻¹ * c ^ (2 ^ k) * l) * l⁻¹ := by group
            _ = 1 := by rw [h1]; group
        exact this
      have hdvd1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hck
      have hdvd2 : orderOf c ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hcO
      have hcop : Nat.Coprime (2 ^ k) (Nat.card O) :=
        Nat.Coprime.pow_left k (Nat.prime_two.coprime_iff_not_dvd.mpr hodd.not_two_dvd_nat)
      have h1 : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
      have hc1 : c = 1 := orderOf_eq_one_iff.mp h1
      have hc1' : x * w * x⁻¹ * w⁻¹ = 1 := hc1
      have : x * w = w * x := by
        calc x * w = x * w * x⁻¹ * w⁻¹ * (w * x) := by group
          _ = w * x := by rw [hc1']; group
      exact this.symm
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZV) hxV
  have hOle : O ≤ mcOf T := by
    calc O = ⨆ (member : V) (_ : member ≠ 1), O ⊓ Subgroup.centralizer ({(member : G)} : Set G) :=
          hgen
      _ ≤ mcOf T := iSup_le fun v => iSup_le fun hv => hterm v hv
  rw [eq_bot_iff, ← hO]
  exact le_inf le_rfl (le_inf (oddCoreIn_le I) hOle)

theorem le_centralizer_of_isPerfect_card_four {K V : Subgroup G} [Group.IsPerfect K]
    (hV : Nat.card V = 4) (hKV : K ≤ Subgroup.normalizer (V : Set G)) :
    K ≤ Subgroup.centralizer (V : Set G) := by
  let ψ : K →* MulAut V := (conjAct V).comp (Subgroup.inclusion hKV)
  have hsolv : Group.IsSolvable (MulAut V) := by
    have : Group.IsSolvable (Equiv.Perm V) := Equiv.Perm.isSolvable (by rw [hV])
    exact Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm V) (by
      intro a b h; exact MulEquiv.ext fun x => congrArg (fun p : Equiv.Perm V => p x) h)
  have hrange : ψ.range = ⊥ := by
    by_contra hne
    have : Nontrivial ψ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
    exact Group.IsPerfect.not_isSolvable ψ.range inferInstance
  intro k hk
  have hk1 : ψ ⟨k, hk⟩ = 1 := by
    have : ψ ⟨k, hk⟩ ∈ ψ.range := ⟨⟨k, hk⟩, rfl⟩
    rw [hrange] at this
    exact Subgroup.mem_bot.mp this
  exact A1b.conjAct_eq_one_iff.mp hk1

omit [Finite G] in
theorem isPerfect_of_isComponentIn {K I : Subgroup G} (hK : IsComponentIn K I) :
    Group.IsPerfect K := by
  have : Group.IsPerfect ↥(K.subgroupOf I) := hK.2.1.1
  exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hK.1).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hK.1).surjective

theorem Setting146.not_le_M_of_isComponentIn (S : Setting146 G T M) {H : Subgroup G}
    (hH : IsHTM T M H) {u : G} (hu : IsInvU T M H u) {I : Subgroup G} (hI : IsIStar T M u I)
    (hsyl : IsSylowTwoOf (T ⊓ I) I) {z : G} (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1)
    {K : Subgroup G} (hK : IsComponentIn K I) : ¬ K ≤ M := by
  intro hKM
  have h115 := S.lemma115Hyp_of_isIStar hH hu hI hsyl hz hz1
  have hnot := (h115.lemma115.2.2 K hK).2
  have hper := isPerfect_of_isComponentIn hK
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _
  have hV4 : Nat.card (VZ T M) = 4 := S.hyp.rank_two
  have hKC := le_centralizer_of_isPerfect_card_four hV4 (hKM.trans hMV)
  exact hnot (hKC.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
    (le_conjClosure _ _ : quasithinOmegaOneCenter T ≤ VZ T M))))

theorem Setting146.lemma_14_6_7_four (S : Setting146 G T M) {H : Subgroup G}
    (hH : IsHTM T M H) {u : G} (hu : IsInvU T M H u) {I : Subgroup G} (hI : IsIStar T M u I)
    (hsyl : IsSylowTwoOf (T ⊓ I) I) {z : G} (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1)
    {K : Subgroup G} (hK : IsComponentIn K I) :
    ¬ K ≤ I ⊓ mcOf T ∧ IsIStar T M u (K ⊔ (T ⊓ I)) := by
  have h115 := S.lemma115Hyp_of_isIStar hH hu hI hsyl hz hz1
  have hnotG : ¬ K ≤ mcOf T := (h115.lemma115.2.2 K hK).2
  have hnotM : ¬ K ≤ M := S.not_le_M_of_isComponentIn hH hu hI hsyl hz hz1 hK
  refine ⟨fun h => hnotG (h.trans inf_le_right), ?_⟩
  have hKI : K ≤ I := hK.1
  have hJI : K ⊔ (T ⊓ I) ≤ I := sup_le hKI inf_le_right
  have hQJ : pCoreOf 2 I ≤ K ⊔ (T ⊓ I) :=
    (pCoreOf_two_le_of_isSylowTwoOf hsyl).trans le_sup_right
  have hQJ' : pCoreOf 2 I ≤ pCoreOf 2 (K ⊔ (T ⊓ I)) :=
    le_pCoreOf_of_le_normalizer hQJ (hJI.trans (le_normalizer_pCoreOf 2 I)) (pCoreOf_isPGroup 2 I)
  have hTu : tU T u ≤ T ⊓ I := le_inf inf_le_left hI.1.1.1
  have hJ : IsI T M u (K ⊔ (T ⊓ I)) :=
    ⟨⟨hTu.trans le_sup_right, fun hbot => hI.1.1.2 (le_bot_iff.mp (hQJ'.trans hbot.le))⟩,
      fun h => hnotG (le_sup_left.trans h), fun h => hnotM (le_sup_left.trans h)⟩
  exact (hI.of_le_inf hJ le_sup_right).1

end CFSG.Quasithin
