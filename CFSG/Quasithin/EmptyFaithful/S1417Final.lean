module

public import CFSG.Quasithin.EmptyFaithful.S1417Core
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1417

section Final

variable {G : Type} [Group G] [Finite G] {T Mc M V : Subgroup G}

omit [Finite G] in
theorem isElemAbelian_sup_of_commute {A B : Subgroup G} (hA : IsElemAbelian 2 A)
    (hB : IsElemAbelian 2 B) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian 2 (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB hc

theorem isTwoReducedIn_sup_VZ (h : quasithinQTFE14Cat G T Mc) (hM : InM T M)
    (hV : IsTwoReducedIn M V) : IsTwoReducedIn M (V ⊔ VZ T M) := by
  obtain ⟨hVT, hTM, hMN, hT'⟩ := core_basic h hM hV
  obtain ⟨S, hS⟩ := h.exists_sylow
  have hF : M ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 M : Set G) ≤ CFSG.Open.pCoreOf 2 M :=
    h.qtke.2.1 M hM.1.1 ⟨S, by rw [hS]; exact hTM⟩
  have hTodd : ¬ 2 ∣ T.relIndex M := hT'.2.2
  have hVZred : IsTwoReducedIn M (VZ T M) :=
    isTwoReducedIn_conjClosure_of_sylowIn hTM h.sylow.1 hTodd hF le_rfl
  obtain ⟨hVZle, hVZel⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn hTM h.sylow.1 hTodd hF
    (Z := quasithinOmegaOneCenter T) le_rfl
  have hVO : V ≤ CFSG.Open.pCoreOf 2 M :=
    le_pCoreOf_of_le_normalizer 2 hV.1 hV.2.1 (B2F.isPGroup_of_isElemAbelian hV.2.2.1)
  have hcomm : ∀ a ∈ V, ∀ b ∈ VZ T M, a * b = b * a := fun a ha b hb =>
    (hVZle hb).2 a (hVO ha)
  refine ⟨sup_le hV.1 hVZred.1, ?_, isElemAbelian_sup_of_commute hV.2.2.1 hVZel hcomm, ?_⟩
  · intro g hg
    rw [B2F.mem_normalizer_iff_cjSub_eq]
    have hgV := B2F.mem_normalizer_iff_cjSub_eq.1 (hV.2.1 hg)
    have hgZ := B2F.mem_normalizer_iff_cjSub_eq.1 (hVZred.2.1 hg)
    unfold cjSub at hgV hgZ ⊢
    rw [Subgroup.map_sup, hgV, hgZ]
  · intro D hDM hDN hD
    have hD' : ∀ d ∈ D, ∃ k : ℕ, d ^ (2 ^ k) ∈ Subgroup.centralizer (V : Set G) := by
      intro d hd
      obtain ⟨k, hk⟩ := hD d hd
      exact ⟨k, Subgroup.centralizer_le (le_sup_left : V ≤ V ⊔ VZ T M) hk⟩
    have hD'' : ∀ d ∈ D, ∃ k : ℕ, d ^ (2 ^ k) ∈ Subgroup.centralizer (VZ T M : Set G) := by
      intro d hd
      obtain ⟨k, hk⟩ := hD d hd
      exact ⟨k, Subgroup.centralizer_le (le_sup_right : VZ T M ≤ V ⊔ VZ T M) hk⟩
    have h1 := hV.2.2.2 D hDM hDN hD'
    have h2 := hVZred.2.2.2 D hDM hDN hD''
    rw [Subgroup.le_centralizer_iff] at h1 h2 ⊢
    exact sup_le h1 h2

theorem core_with_Z (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) (hV : IsTwoReducedIn M V)
    (hJ : ¬ thompsonJ T ≤ M ⊓ Subgroup.centralizer (V : Set G))
    (hcase : M ≠ Mc ∨ Nat.card (quasithinOmegaOneCenter T) = 2)
    (hperf : ∀ V' : Subgroup G, IsTwoReducedIn M V' →
      perfectCore M ≤ Subgroup.centralizer (V' : Set G)) :
    quasithinOmegaOneCenter T ≤ omegaOneCenterOf (thompsonJ T) ⊓ V ∧
      Nat.card (quasithinOmegaOneCenter T) = 2 ∧
        CoreConcl T M V (quasithinOmegaOneCenter T ≤ omegaOneCenterOf (thompsonJ T) ⊓ V ∧
          Nat.card (quasithinOmegaOneCenter T) = 2) := by
  obtain ⟨hVT, hTM, hMN, hT'⟩ := core_basic h hM hV
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTM.trans hMN
  have hVe : IsElemAbelian 2 V := hV.2.2.1
  have hZT : quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
    (Subgroup.closure_le _).2 fun z hz => hz.1
  have hV' := isTwoReducedIn_sup_VZ h hM hV
  have hJ' : ¬ thompsonJ T ≤ M ⊓ Subgroup.centralizer ((V ⊔ VZ T M : Subgroup G) : Set G) :=
    fun hh => hJ fun x hx => ⟨(hh hx).1, Subgroup.centralizer_le (le_sup_left : V ≤ V ⊔ VZ T M)
      (hh hx).2⟩
  have hcore' := core h hM hV' hJ' hcase (hperf _ hV') True trivial
  have hZV' : quasithinOmegaOneCenter T ≤ (V ⊔ VZ T M) ⊓ Subgroup.centralizer (T : Set G) :=
    le_inf ((le_conjClosure (quasithinOmegaOneCenter T) M).trans le_sup_right)
      (hZT.trans inf_le_right)
  have hZ2 : Nat.card (quasithinOmegaOneCenter T) = 2 := by
    have hle : Nat.card (quasithinOmegaOneCenter T) ≤ 2 :=
      (Subgroup.card_le_of_le hZV').trans hcore'.2.1
    have hne : quasithinOmegaOneCenter T ≠ ⊥ := h.omegaOneCenter_ne_bot
    have hge : 2 ≤ Nat.card (quasithinOmegaOneCenter T) := by
      by_contra hlt
      have h1 : Nat.card (quasithinOmegaOneCenter T) = 1 := by
        have := Nat.card_pos (α := ↥(quasithinOmegaOneCenter T))
        omega
      exact hne (Subgroup.eq_bot_of_card_eq _ h1)
    omega
  have hVne : V ≠ ⊥ := by
    intro hb
    apply hJ
    refine le_inf ((iSup₂_le fun _ hA => hA.1 : thompsonJ T ≤ T).trans hTM) ?_
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hb, SetLike.mem_coe, Subgroup.mem_bot] at hy
    rw [hy]
    simp
  have htop : (⊤ : Subgroup (IntMod V hVe)) ≠ ⊥ := by
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hVne
    intro htb
    have : (IntMod.mk hVe a) ∈ (⊤ : Subgroup (IntMod V hVe)) := Subgroup.mem_top _
    rw [htb, Subgroup.mem_bot] at this
    exact ha1 this
  obtain ⟨u, -, hu1, huZ⟩ := exists_Z_of_stable h hVe hVT hTN (U := ⊤) htop
    (fun g _ u _ => Subgroup.mem_top _)
  have hZV : quasithinOmegaOneCenter T ≤ V := by
    obtain ⟨s, -, -, hsu⟩ := exists_eq_of_card_eq_two hZ2
    have hu1' : u.val ≠ 1 := fun h1 => hu1 (IntMod.val_injective (by simpa using h1))
    have hus : u.val = s := (hsu _ huZ).resolve_left hu1'
    intro x hx
    rcases hsu x hx with h1 | h1
    · rw [h1]
      exact V.one_mem
    · rw [h1, ← hus]
      exact IntMod.val_mem u
  have hZE : quasithinOmegaOneCenter T ≤ omegaOneCenterOf (thompsonJ T) ⊓ V :=
    le_inf (omegaOneCenter_le_omegaOneCenterOf T) hZV
  exact ⟨hZE, hZ2, core h hM hV hJ hcase (hperf V hV) _ ⟨hZE, hZ2⟩⟩

theorem stageLemma1417_of_stageLemma1416 (h16 : StageLemma1416) : StageLemma1417 := by
  intro G _ _ T Mc h M V hM hV hJ hcase
  have hperf : ∀ V' : Subgroup G, IsTwoReducedIn M V' →
      perfectCore M ≤ Subgroup.centralizer (V' : Set G) := fun V' hV' =>
    (h16 G T Mc h).1 M V' hM hV'
  obtain ⟨hZE, hZ2, hcore⟩ := core_with_Z h hM hV hJ hcase hperf
  rcases hcore.1 with ⟨h4, hTop, hE2⟩ | hC2
  · left
    refine ⟨h4, hTop, ?_, hZ2⟩
    exact (Subgroup.eq_of_le_of_card_ge hZE (by rw [hE2, hZ2])).symm
  · right
    exact (lemma1417CaseTwo_iff T M V).2 hC2

theorem le_of_isPGroup_of_isSylowTwoOf {X T' P : Subgroup G} (hT : IsSylowTwoOf T' X)
    (hPX : P ≤ X) (hTP : T' ≤ P) (hP2 : IsPGroup 2 P) : P ≤ T' := by
  have h1 : T'.relIndex P * P.relIndex X = T'.relIndex X :=
    Subgroup.relIndex_mul_relIndex T' P X hTP hPX
  have hodd : ¬ 2 ∣ T'.relIndex X := hT.2.2
  have hodd' : ¬ 2 ∣ T'.relIndex P := fun hd => hodd (h1 ▸ dvd_mul_of_dvd_left hd _)
  obtain ⟨n, hn⟩ := hP2.index (T'.subgroupOf P)
  have hn' : T'.relIndex P = 2 ^ n := hn
  cases n with
  | zero => exact Subgroup.relIndex_eq_one.mp (by simpa using hn')
  | succ n => exact absurd (hn' ▸ dvd_pow_self 2 (Nat.succ_ne_zero n)) hodd'

theorem stab_of_core (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) (hV : IsTwoReducedIn M V)
    (hJ : ¬ thompsonJ T ≤ M ⊓ Subgroup.centralizer (V : Set G))
    (hcase : M ≠ Mc ∨ Nat.card (quasithinOmegaOneCenter T) = 2)
    (hperf : ∀ V' : Subgroup G, IsTwoReducedIn M V' →
      perfectCore M ≤ Subgroup.centralizer (V' : Set G)) :
    M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      (M ⊓ Subgroup.centralizer (V : Set G)) ⊔ T := by
  obtain ⟨hZE, hZ2, hcore⟩ := core_with_Z h hM hV hJ hcase hperf
  have hZV : quasithinOmegaOneCenter T ≤ V := hZE.trans inf_le_right
  have hodd := hcore.2.2
  obtain ⟨hVT, hTM, hMN, hT'⟩ := core_basic h hM hV
  have hVe : IsElemAbelian 2 V := hV.2.2.1
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTM.trans hMN
  have hZT : quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
    (Subgroup.closure_le _).2 fun z hz => hz.1
  have hTbar : IsSylowTwoOf (autI hVe T) (autI hVe M) := B2F.isSylowTwoOf_autI hVe hMN hT'
  intro m hm
  obtain ⟨hmM, hmZ⟩ := hm
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h.omegaOneCenter_ne_bot
  have hz1' : z ≠ 1 := fun e => hz1 (Subtype.ext e)
  let v' : V := ⟨z, hZV hzZ⟩
  let v : IntMod V hVe := v'
  have hv1 : v' ≠ 1 := fun e => hz1' (congrArg Subtype.val e)
  have hmN : m ∈ Subgroup.normalizer (V : Set G) := hMN hmM
  have hfixm : convI hVe ⟨m, hmN⟩ v = v := by
    apply IntMod.val_injective
    rw [convI_apply_val]
    show m * z * m⁻¹ = z
    have := Subgroup.mem_centralizer_iff.mp hmZ z hzZ
    rw [← this, mul_inv_cancel_right]
  have hvT : v ∈ fixV (autI hVe T) := (mem_fixV_autI hVe hTN v).2 (hZT hzZ).2
  set P : Subgroup (MulAut (IntMod V hVe)) :=
    autI hVe M ⊓ MulAction.stabilizer (MulAut (IntMod V hVe)) v with hP
  have hPp : IsPGroup 2 P := by
    intro g
    obtain ⟨k, mm, hmm, hn⟩ := Nat.exists_eq_two_pow_mul_odd
      (n := orderOf (g : MulAut (IntMod V hVe))) (orderOf_pos _).ne'
    refine ⟨k, ?_⟩
    set g₀ : MulAut (IntMod V hVe) := (g : MulAut (IntMod V hVe)) with hg₀
    have hh₀P : g₀ ^ (2 ^ k) ∈ P := P.pow_mem g.2 _
    have hord : orderOf (g₀ ^ (2 ^ k)) = mm := by
      rw [orderOf_pow_of_dvd (by positivity) ⟨mm, hn⟩, hn, Nat.mul_div_cancel_left _
        (by positivity)]
    have hfix : (g₀ ^ (2 ^ k)) v = v := by
      have := (MulAction.mem_stabilizer_iff.mp hh₀P.2)
      exact this
    have h1 : g₀ ^ (2 ^ k) = 1 :=
      hodd v' (hZT hzZ).2 hv1 (g₀ ^ (2 ^ k)) hh₀P.1 (hord ▸ hmm) hfix
    exact Subtype.ext (by simpa using h1)
  have hTP : autI hVe T ≤ P := fun g hg =>
    ⟨autI_mono hVe hTM hg, MulAction.mem_stabilizer_iff.mpr (hvT g hg)⟩
  have hPT : P ≤ autI hVe T := le_of_isPGroup_of_isSylowTwoOf hTbar inf_le_left hTP hPp
  have hmP : convI hVe ⟨m, hmN⟩ ∈ P :=
    ⟨convI_mem_autI hVe hmM hmN, MulAction.mem_stabilizer_iff.mpr hfixm⟩
  obtain ⟨t₀, ht₀, ht₀eq⟩ := (mem_autI hVe).1 (hPT hmP)
  set a : Subgroup.normalizer (V : Set G) := ⟨m, hmN⟩ with ha
  set kN : Subgroup.normalizer (V : Set G) := a * t₀⁻¹ with hkN
  have hkG : (kN : G) = m * (t₀ : G)⁻¹ := rfl
  have hkM : (kN : G) ∈ M := by
    rw [hkG]
    exact M.mul_mem hmM (M.inv_mem (hTM ht₀))
  have hkC : (kN : G) ∈ Subgroup.centralizer (V : Set G) := by
    refine (convI_eq_one_iff hVe kN).1 ?_
    rw [hkN, map_mul, map_inv, ht₀eq]
    group
  have hm_eq : m = (kN : G) * (t₀ : G) := by
    rw [hkG]
    group
  rw [hm_eq]
  exact Subgroup.mul_mem_sup ⟨hkM, hkC⟩ ht₀

end Final

end S1417

end CFSG.Quasithin
