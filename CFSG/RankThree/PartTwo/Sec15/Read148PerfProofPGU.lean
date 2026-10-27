module

public import CFSG.RankThree.PartTwo.Sec15.Read148PerfProofPGL
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item148StepPGLAbel
import CFSG.RankThree.PartTwo.Sec14.Item148Res6ProofPGLFacts
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofCentral
import CFSG.RankThree.PartTwo.Sec17.Item17Res2ProofL3Two
import CFSG.RankThree.PartTwo.KFacts.KS14PGL

public section

namespace CFSG.RankThree.PartTwo.Sec15.Read148Perf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

theorem isoLThreePi_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X') {p n : ℕ}
    [Fact p.Prime] (h : Sec4.IsoLThreePi X' p n) : Sec4.IsoLThreePi X p n := by
  rcases h with ⟨h1, ⟨φ⟩⟩ | ⟨h1, ⟨φ⟩⟩
  · exact Or.inl ⟨h1, ⟨e.trans φ⟩⟩
  · exact Or.inr ⟨h1, ⟨e.trans φ⟩⟩

theorem exists_pgu_structure {P : Type} [Group P] [Finite P] {p f : ℕ}
    (h : Sec14.IsZ3PGLThreeAt P p f) (h2 : p ^ f = 2) :
    ∃ S V : Subgroup P, S.Normal ∧ (∀ y : P, y ^ 3 ∈ S) ∧ S.index ≤ 9 ∧ V ≤ S ∧
      (∀ v ∈ V, v ^ 3 = 1) ∧ (∀ s ∈ S, ∀ k : ℕ, s ^ 3 ^ k = 1 → s ∈ V) ∧
      S ≤ Subgroup.normalizer (V : Set P) ∧
      (∀ x ∈ V, x ≠ 1 → ∀ t ∈ S, t * x = x * t → t ∈ V) := by
  obtain ⟨π, K, _, hK, hq, ⟨ψ⟩⟩ := h
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hSG : projImage (slPi π 3 (p ^ f) K) ≤ projImage (glPi π 3 (p ^ f) K) :=
    Subgroup.map_mono (slPi_le_glPi hπ)
  set PG := projImage (glPi π 3 (p ^ f) K) with hPG
  set PS := projImage (slPi π 3 (p ^ f) K) with hPS
  set PS' : Subgroup ↥PG := PS.subgroupOf PG with hPS'
  have hPSn : PS'.Normal := by
    refine Subgroup.Normal.of_commutator_le ↥PG fun x hx => ?_
    rw [hPS', Subgroup.mem_subgroupOf]
    have hx' : (x : ProjGenLinGroup (Fin 3) K) ∈ ⁅PG, PG⁆ := by
      rw [← map_subtype_commutator]
      exact ⟨x, hx, rfl⟩
    exact Sec14.Item148PtRes2.commutator_projImage_glPi_le hπ hx'
  set N : Subgroup (Multiplicative (ZMod 3) × ↥PG) :=
    (⊥ : Subgroup (Multiplicative (ZMod 3))).prod PS' with hN
  set S : Subgroup P := N.comap ψ.toMonoidHom with hS
  have hcube : ∀ y : P, y ^ 3 ∈ S := by
    intro y
    rw [hS, Subgroup.mem_comap, map_pow, hN, Subgroup.mem_prod]
    constructor
    · rw [Subgroup.mem_bot, Prod.pow_fst]
      have h0 := pow_card_eq_one' (x := (ψ.toMonoidHom y).1)
      rwa [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at h0
    · rw [Prod.pow_snd, hPS', Subgroup.mem_subgroupOf]
      exact pow_three_mem_projImage_slPi hK hq _
  have hPSi : PS'.index ≤ 3 := by
    obtain ⟨δ, hδ⟩ := Sec14.exists_detPow_projImage (glPi π 3 (p ^ f) K) (qSubPi π (p ^ f) / 3)
      (Sec14.Item148Res6.detPow_eq_one_of_mem_center hK hq)
    have hker : δ.ker ≤ PS' := by
      rintro ⟨_, A, hA, rfl⟩ hx
      rw [MonoidHom.mem_ker, hδ A hA] at hx
      rw [hPS', Subgroup.mem_subgroupOf]
      exact Sec14.Item148Res6.mk_mem_projImage_slPi_of_detPow hK hq hA hx
    have hK3 : Nat.card Kˣ = 3 := by
      rw [Nat.card_units, hK.card, h2]
      cases π
      · rfl
      · exfalso
        change (p ^ f) % 3 = 1 at hq
        rw [h2] at hq
        norm_num at hq
    have hr : Nat.card δ.range ≤ 3 := (Subgroup.card_le_card_group δ.range).trans hK3.le
    have hdvd := Subgroup.index_dvd_of_le hker
    rw [Subgroup.index_ker] at hdvd
    exact (Nat.le_of_dvd Nat.card_pos hdvd).trans hr
  have hindex : S.index ≤ 9 := by
    rw [hS, Subgroup.index_comap_of_surjective _ ψ.surjective, hN, Subgroup.index_prod,
      Subgroup.index_bot, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    omega
  have e1 : ↥S ≃* ↥N := (S.equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective ψ.surjective N))
  have e2 : ↥N ≃* ↥PS' :=
    { toFun := fun x => ⟨(x : Multiplicative (ZMod 3) × ↥PG).2, (Subgroup.mem_prod.mp x.2).2⟩
      invFun := fun y => ⟨(1, y), Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, y.2⟩⟩
      left_inv := fun x => by
        obtain ⟨⟨z, y⟩, hz, hy⟩ := x
        have : z = 1 := (Subgroup.mem_bot).mp hz
        subst this
        rfl
      right_inv := fun y => rfl
      map_mul' := fun x y => rfl }
  obtain ⟨hp, hiso⟩ := Sec13.ResProof.isoLThreePi_projImage_slPi hK hq
  have hisoS : Sec4.IsoLThreePi ↥S p f :=
    isoLThreePi_of_mulEquiv ((e1.trans e2).trans (Subgroup.subgroupOfEquivOfLe hSG)) hiso
  obtain ⟨T⟩ := (Sylow.nonempty : Nonempty (Sylow 3 ↥S))
  obtain ⟨-, -, hT3, hTn, hTc⟩ := Sec17.Proof17Res2.u32_structure hK.one_le hisoS h2 T
  refine ⟨S, (T : Subgroup ↥S).map S.subtype, Subgroup.normal_comap _, hcube, hindex,
    Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    have h1 := congrArg Subtype.val (hT3 t ht)
    simpa using h1
  · intro s hs k hk
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have htk : (⟨s, hs⟩ : ↥S) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one htk)
    have hpg : IsPGroup 3 (Subgroup.zpowers (⟨s, hs⟩ : ↥S)) :=
      IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    obtain ⟨T', hT'⟩ := hpg.exists_le_sylow
    have : Unique (Sylow 3 ↥S) := Sylow.unique_of_normal T hTn
    have hTT : T' = T := Subsingleton.elim _ _
    have hsT : (⟨s, hs⟩ : ↥S) ∈ (T : Subgroup ↥S) := hTT ▸ hT' (Subgroup.mem_zpowers _)
    exact ⟨_, hsT, rfl⟩
  · refine le_normalizer_of_conj fun g hg v hv => ?_
    obtain ⟨t, ht, rfl⟩ := hv
    exact ⟨_, hTn.conj_mem t ht ⟨g, hg⟩, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ hx1 t ht htx
    have hx1' : x ≠ 1 := fun h => hx1 (by rw [h, map_one])
    exact ⟨_, hTc x hx hx1' ⟨t, ht⟩ (Subtype.ext htx), rfl⟩

theorem exists_pgu_structure_ambient {Γ : Type} [Group Γ] [Finite Γ] {P : Subgroup Γ} {p f : ℕ}
    (hZ : Sec14.IsZ3PGLThreeAt ↥P p f) (h2 : p ^ f = 2) :
    ∃ S V : Subgroup Γ, S ≤ P ∧ P ≤ Subgroup.normalizer (S : Set Γ) ∧ (∀ y ∈ P, y ^ 3 ∈ S) ∧
      (∀ E : Subgroup Γ, E ≤ P → Nat.card E = 27 → ∃ e ∈ E, e ∈ S ∧ e ≠ 1) ∧ V ≤ S ∧
      (∀ v ∈ V, v ^ 3 = 1) ∧ (∀ s ∈ S, ∀ k : ℕ, s ^ 3 ^ k = 1 → s ∈ V) ∧
      S ≤ Subgroup.normalizer (V : Set Γ) ∧
      (∀ x ∈ V, x ≠ 1 → ∀ t ∈ S, t * x = x * t → t ∈ V) := by
  obtain ⟨S₀, V₀, hS₀, hcube, hindex, hVS, hV3, hV3k, hSV, hcent⟩ := exists_pgu_structure hZ h2
  refine ⟨S₀.map P.subtype, V₀.map P.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_,
    Subgroup.map_mono hVS, ?_, ?_, ?_, ?_⟩
  · refine le_normalizer_of_conj fun g hg s hs => ?_
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    exact ⟨_, hS₀.conj_mem s₀ hs₀ ⟨g, hg⟩, rfl⟩
  · intro y hy
    exact ⟨_, hcube ⟨y, hy⟩, rfl⟩
  · intro E hE hE27
    by_contra hcon
    push Not at hcon
    set E' := E.subgroupOf P
    have hE' : Nat.card E' = 27 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv, hE27]
    set φ : ↥E' →* ↥P ⧸ S₀ := (QuotientGroup.mk' S₀).comp E'.subtype
    have hφ : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      have h1 : ((x : ↥P) : Γ) = 1 := hcon _ (Subgroup.mem_subgroupOf.mp x.2) ⟨_, hx, rfl⟩
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext h1))
    have h1 := Nat.card_le_card_of_injective φ hφ
    rw [hE', ← Subgroup.index_eq_card] at h1
    omega
  · rintro _ ⟨v, hv, rfl⟩
    have h1 := congrArg Subtype.val (hV3 v hv)
    simpa using h1
  · rintro _ ⟨s, hs, rfl⟩ k hk
    exact ⟨s, hV3k s hs k (Subtype.ext (by simpa using hk)), rfl⟩
  · refine le_normalizer_of_conj fun g hg v hv => ?_
    obtain ⟨g₀, hg₀, rfl⟩ := hg
    obtain ⟨v₀, hv₀, rfl⟩ := hv
    have h1 := (Subgroup.mem_normalizer_iff.mp (hSV hg₀) v₀).mp hv₀
    exact ⟨_, h1, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ hx1 _ ⟨t, ht, rfl⟩ htx
    have hx1' : x ≠ 1 := fun h => hx1 (by rw [h, map_one])
    exact ⟨t, hcent x hx hx1' t ht (Subtype.ext htx), rfl⟩

section Coprime

variable {Γ : Type} [Group Γ]

theorem eq_one_of_pow_three_of_coprime {y : Γ} (hy3 : y ^ 3 = 1)
    (hco : Nat.Coprime (orderOf y) 3) : y = 1 :=
  orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hco (orderOf_dvd_of_pow_eq_one hy3))

theorem eq_bot_of_le_normalizer_of_coprime {S V R : Subgroup Γ}
    (hSV : S ≤ Subgroup.normalizer (V : Set Γ)) (hV3 : ∀ v ∈ V, v ^ 3 = 1)
    (hcent : ∀ x ∈ V, x ≠ 1 → ∀ t ∈ S, t * x = x * t → t ∈ V) (hRS : R ≤ S)
    (hR3 : Nat.Coprime (Nat.card R) 3) {v : Γ} (hvV : v ∈ V) (hv1 : v ≠ 1)
    (hvR : v ∈ Subgroup.normalizer (R : Set Γ)) : R = ⊥ := by
  have htriv : ∀ r ∈ R, r ∈ V → r = 1 := fun r hr hrV =>
    eq_one_of_pow_three_of_coprime (hV3 r hrV)
      (Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard R hr) hR3)
  rw [eq_bot_iff]
  intro r hr
  have hcV : r * v * r⁻¹ * v⁻¹ ∈ V :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp (hSV (hRS hr)) v).mp hvV) (inv_mem hvV)
  have hcR : r * v * r⁻¹ * v⁻¹ ∈ R := by
    have h1 := (Subgroup.mem_normalizer_iff.mp hvR r⁻¹).mp (inv_mem hr)
    rw [show r * v * r⁻¹ * v⁻¹ = r * (v * r⁻¹ * v⁻¹) by group]
    exact mul_mem hr h1
  have hc1 := htriv _ hcR hcV
  have hrv : r * v = v * r := by
    calc r * v = r * v * r⁻¹ * v⁻¹ * (v * r) := by group
      _ = v * r := by rw [hc1, one_mul]
  exact Subgroup.mem_bot.mpr (htriv r hr (hcent v hvV hv1 r (hRS hr) hrv))

theorem coprime_card_of_inf_eq_bot [Finite Γ] {S V D : Subgroup Γ}
    (hV3k : ∀ s ∈ S, ∀ k : ℕ, s ^ 3 ^ k = 1 → s ∈ V) (hDS : D ≤ S) (hDV : D ⊓ V = ⊥) :
    Nat.Coprime (Nat.card D) 3 := by
  refine ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => ?_).symm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := D) 3 h3
  have hd3 : (d : Γ) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← hd, pow_orderOf_eq_one, Subgroup.coe_one]
  have hdV : (d : Γ) ∈ V := hV3k _ (hDS d.2) 1 (by rwa [pow_one])
  have h1 : (d : Γ) ∈ D ⊓ V := Subgroup.mem_inf.mpr ⟨d.2, hdV⟩
  rw [hDV, Subgroup.mem_bot] at h1
  have h2 : d = 1 := Subtype.ext h1
  rw [h2, orderOf_one] at hd
  norm_num at hd

end Coprime

theorem false_of_isZ3PGLThreeAt_two {Γ : Type} [Group Γ] [Finite Γ]
    {X J₁ J₂ B : Subgroup Γ} {S : Set (Subgroup Γ)} (hsup : J₁ ⊔ J₂ = X) (hinf : J₁ ⊓ J₂ = ⊥)
    (hcomm : ⁅J₁, J₂⁆ = ⊥) (hB : IsMulCommutative ↥B)
    (hBX : B ≤ Subgroup.normalizer (X : Set Γ)) (hB27 : Nat.card B = 27) (hXS : X ≤ sSup S)
    (hSX : ∀ Q ∈ S, Q ≤ X) (hS3 : ∀ Q ∈ S, Nat.Coprime (Nat.card Q) 3)
    (hSB : ∀ Q ∈ S, B ≤ Subgroup.normalizer (Q : Set Γ)) {p f : ℕ}
    (hZ : Sec14.IsZ3PGLThreeAt ↥(J₁ ⊔ B) p f) (h2 : p ^ f = 2) : False := by
  obtain ⟨U, V, -, hPU, hcube, hE, -, hV3, hV3k, hUV, hcent⟩ :=
    exists_pgu_structure_ambient hZ h2
  have hJX₁ : J₁ ≤ X := hsup ▸ le_sup_left
  have hJX₂ : J₂ ≤ X := hsup ▸ le_sup_right
  have hJ₁P : J₁ ≤ J₁ ⊔ B := le_sup_left
  have hBP : B ≤ J₁ ⊔ B := le_sup_right
  have hC₁ : J₁ ≤ Subgroup.centralizer (J₂ : Set Γ) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hC₂ : J₂ ≤ Subgroup.centralizer (J₁ : Set Γ) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcomm
  have hXN₂ : X ≤ Subgroup.normalizer (J₂ : Set Γ) := by
    rw [← hsup]
    exact sup_le (hC₁.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hmemJ : ∀ x ∈ J₁ ⊓ J₂, x = 1 := fun x hx => by
    rw [hinf] at hx
    exact Subgroup.mem_bot.mp hx
  have hJ₁ : J₁ ≠ ⊥ := by
    intro hJb
    obtain ⟨a, b, hab⟩ := KFacts.KS14.ks15Z3PGLNonabelian _ p f hZ
    apply hab
    have hPB : J₁ ⊔ B = B := by rw [hJb, bot_sup_eq]
    have ha : (a : Γ) ∈ B := hPB.le a.2
    have hb : (b : Γ) ∈ B := hPB.le b.2
    have h := congrArg Subtype.val (hB.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    exact Subtype.ext (by simpa using h)
  set T := Subgroup.closure {j : Γ | j ∈ J₁ ∧ Nat.Coprime (orderOf j) 3} with hT
  have hTJ : T ≤ J₁ := (Subgroup.closure_le _).mpr fun j hj => hj.1
  have hTU : T ≤ U := (Subgroup.closure_le _).mpr fun j hj => by
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hj.2.symm
    rw [SetLike.mem_coe, ← hm]
    exact pow_mem (hcube j (hJ₁P hj.1)) m
  have hXT : X ≤ T ⊔ J₂ := by
    refine hXS.trans (sSup_le fun Q hQ q hq => ?_)
    obtain ⟨j₁, hj₁, j₂, hj₂, hq'⟩ := exists_mul_of_mem_sup hcomm (hsup.symm ▸ hSX Q hQ hq)
    have hn : j₁ ^ orderOf q = 1 := by
      have h1 : (j₁ * j₂) ^ orderOf q = 1 := by
        rw [hq']
        exact pow_orderOf_eq_one q
      rw [(commute_of_commutator_eq_bot hcomm hj₁ hj₂).mul_pow] at h1
      refine hmemJ _ (Subgroup.mem_inf.mpr ⟨pow_mem hj₁ _, ?_⟩)
      rw [eq_inv_of_mul_eq_one_left h1]
      exact inv_mem (pow_mem hj₂ _)
    have hco : Nat.Coprime (orderOf j₁) 3 :=
      Nat.Coprime.coprime_dvd_left ((orderOf_dvd_of_pow_eq_one hn).trans
        (Subgroup.orderOf_dvd_natCard Q hq)) (hS3 Q hQ)
    rw [← hq']
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨hj₁, hco⟩))
      (Subgroup.mem_sup_right hj₂)
  have hJT : J₁ ≤ T := by
    intro j hj
    have hcommT : ⁅T, J₂⁆ = ⊥ := le_bot_iff.mp (hcomm ▸ Subgroup.commutator_mono hTJ le_rfl)
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup hcommT (hXT (hJX₁ hj))
    have hb1 : b = 1 := hmemJ b (Subgroup.mem_inf.mpr ⟨by
      rw [show b = a⁻¹ * j by rw [← hab, inv_mul_cancel_left]]
      exact mul_mem (inv_mem (hTJ ha)) hj, hb⟩)
    rw [← hab, hb1, mul_one]
    exact ha
  have hJU : J₁ ≤ U := hJT.trans hTU
  obtain ⟨u, hu, hu1, hu3⟩ : ∃ u ∈ J₁, u ≠ 1 ∧ Nat.Coprime (orderOf u) 3 := by
    by_contra hcon
    push Not at hcon
    apply hJ₁
    rw [eq_bot_iff]
    refine hJT.trans ((Subgroup.closure_le _).mpr fun j hj => ?_)
    by_contra hj1
    exact hj1 (Subgroup.mem_bot.mpr (by_contra fun hne => hne (hcon j hj.1 hne hj.2 |>.elim)))
  obtain ⟨v, hvB, hvU, hv1⟩ := hE B hBP hB27
  have hvV : v ∈ V := hV3k v hvU 3 (by
    have h1 := congrArg Subtype.val (pow_card_eq_one' (x := (⟨v, hvB⟩ : ↥B)))
    rw [hB27] at h1
    simpa using h1)
  have hKL : ∀ R : Subgroup Γ, R ≤ U → Nat.Coprime (Nat.card R) 3 →
      B ≤ Subgroup.normalizer (R : Set Γ) → R = ⊥ := fun R hRU hR3 hBR =>
    eq_bot_of_le_normalizer_of_coprime hUV hV3 hcent hRU hR3 hvV hv1 (hBR hvB)
  have hVtriv : ∀ y ∈ V, Nat.Coprime (orderOf y) 3 → y = 1 := fun y hy hco =>
    eq_one_of_pow_three_of_coprime (hV3 y hy) hco
  have hBD : B ≤ Subgroup.normalizer ((X ⊓ U : Subgroup Γ) : Set Γ) :=
    le_normalizer_of_conj fun b hb x hx => Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp (hBX hb) x).mp (Subgroup.mem_inf.mp hx).1,
        (Subgroup.mem_normalizer_iff.mp (hPU (hBP hb)) x).mp (Subgroup.mem_inf.mp hx).2⟩
  have hW : J₂ ⊓ U = ⊥ := by
    rcases Subgroup.bot_or_exists_ne_one (J₂ ⊓ U) with h | ⟨w, hw, hw1⟩
    · exact h
    exfalso
    obtain ⟨hwJ, hwU⟩ := Subgroup.mem_inf.mp hw
    have hWV : ∀ w' ∈ J₂, w' ∈ V → w' = 1 := fun w' hw'J hw'V => by
      by_contra hne
      exact hu1 (hVtriv u (hcent w' hw'V hne u (hJU hu)
        (commute_of_commutator_eq_bot hcomm hu hw'J).eq) hu3)
    have hJV : ∀ s ∈ J₁, s ∈ V → s = 1 := fun s hsJ hsV => by
      by_contra hne
      exact hw1 (hWV w hwJ (hcent s hsV hne w hwU
        (commute_of_commutator_eq_bot hcomm hsJ hwJ).eq.symm))
    have hDV : (X ⊓ U) ⊓ V = ⊥ := by
      rw [eq_bot_iff]
      intro d hd
      obtain ⟨hdXU, hdV⟩ := Subgroup.mem_inf.mp hd
      obtain ⟨hdX, hdU⟩ := Subgroup.mem_inf.mp hdXU
      obtain ⟨j, hj, w', hw', rfl⟩ := exists_mul_of_mem_sup hcomm (hsup.symm ▸ hdX)
      have hc := commute_of_commutator_eq_bot hcomm hj hw'
      have hj3 : j ^ 3 = 1 := by
        have h1 := hV3 _ hdV
        rw [hc.mul_pow] at h1
        refine hmemJ _ (Subgroup.mem_inf.mpr ⟨pow_mem hj _, ?_⟩)
        rw [eq_inv_of_mul_eq_one_left h1]
        exact inv_mem (pow_mem hw' _)
      have hj1 : j = 1 := hJV j hj (hV3k j (hJU hj) 1 (by rwa [pow_one]))
      rw [hj1, one_mul] at hdV ⊢
      exact Subgroup.mem_bot.mpr (hWV w' hw' hdV)
    have hD := hKL (X ⊓ U) inf_le_right (coprime_card_of_inf_eq_bot hV3k inf_le_right hDV) hBD
    apply hJ₁
    rw [eq_bot_iff, ← hD]
    exact le_inf hJX₁ hJU
  have hDJ : X ⊓ U = J₁ := by
    refine le_antisymm (fun x hx => ?_) (le_inf hJX₁ hJU)
    obtain ⟨hxX, hxU⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨j₁, hj₁, j₂, hj₂, rfl⟩ := exists_mul_of_mem_sup hcomm (hsup.symm ▸ hxX)
    have hj₂U : j₂ ∈ U := by
      rw [show j₂ = j₁⁻¹ * (j₁ * j₂) by rw [inv_mul_cancel_left]]
      exact mul_mem (inv_mem (hJU hj₁)) hxU
    have h1 : j₂ ∈ J₂ ⊓ U := Subgroup.mem_inf.mpr ⟨hj₂, hj₂U⟩
    rw [hW, Subgroup.mem_bot] at h1
    rw [h1, mul_one]
    exact hj₁
  have hBN₁ : B ≤ Subgroup.normalizer (J₁ : Set Γ) := hDJ ▸ hBD
  obtain ⟨s, hsJV, hs1⟩ : ∃ s ∈ J₁ ⊓ V, s ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one (J₁ ⊓ V) with h | h
    · exact (hJ₁ (hKL J₁ hJU (coprime_card_of_inf_eq_bot hV3k hJU h) hBN₁)).elim
    · exact h
  obtain ⟨hsJ, hsV⟩ := Subgroup.mem_inf.mp hsJV
  have hJ₂eq : ∀ x ∈ X, x ∈ Subgroup.centralizer (J₁ : Set Γ) → x ∈ J₂ := by
    intro x hx hxc
    obtain ⟨j₁, hj₁, j₂, hj₂, rfl⟩ := exists_mul_of_mem_sup hcomm (hsup.symm ▸ hx)
    have hj₁c : j₁ ∈ Subgroup.centralizer (J₁ : Set Γ) := by
      rw [show j₁ = j₁ * j₂ * j₂⁻¹ by rw [mul_inv_cancel_right]]
      exact mul_mem hxc (inv_mem (hC₂ hj₂))
    have hj₁V : j₁ ∈ V :=
      hcent s hsV hs1 j₁ (hJU hj₁) (Subgroup.mem_centralizer_iff.mp hj₁c s hsJ).symm
    have hj₁1 : j₁ = 1 := by
      by_contra hne
      exact hu1 (hVtriv u (hcent j₁ hj₁V hne u (hJU hu)
        (Subgroup.mem_centralizer_iff.mp hj₁c u hu)) hu3)
    rw [hj₁1, one_mul]
    exact hj₂
  have hBN₂ : B ≤ Subgroup.normalizer (J₂ : Set Γ) := by
    refine le_normalizer_of_conj fun b hb x hx => hJ₂eq _ ?_ ?_
    · exact (Subgroup.mem_normalizer_iff.mp (hBX hb) x).mp (hJX₂ hx)
    · refine Subgroup.mem_centralizer_iff.mpr fun j hj => ?_
      have hj' : b⁻¹ * j * b ∈ J₁ := by
        have h1 := (Subgroup.mem_normalizer_iff.mp (hBN₁ (inv_mem hb)) j).mp hj
        rwa [inv_inv] at h1
      have hxj : (b⁻¹ * j * b) * x = x * (b⁻¹ * j * b) :=
        Subgroup.mem_centralizer_iff.mp (hC₂ hx) _ hj'
      calc j * (b * x * b⁻¹) = b * ((b⁻¹ * j * b) * x) * b⁻¹ := by group
        _ = b * (x * (b⁻¹ * j * b)) * b⁻¹ := by rw [hxj]
        _ = b * x * b⁻¹ * j := by group
  have hQJ : ∀ Q ∈ S, Q ≤ J₂ := by
    intro Q hQ
    have hQN : Q ≤ Subgroup.normalizer (J₂ : Set Γ) := (hSX Q hQ).trans hXN₂
    have hBQJ : B ≤ Subgroup.normalizer ((Q ⊔ J₂ : Subgroup Γ) : Set Γ) :=
      Sec14.le_normalizer_sup (hSB Q hQ) hBN₂
    have hBR : B ≤ Subgroup.normalizer (((Q ⊔ J₂) ⊓ J₁ : Subgroup Γ) : Set Γ) :=
      le_normalizer_of_conj fun b hb x hx => Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp (hBQJ hb) x).mp (Subgroup.mem_inf.mp hx).1,
          (Subgroup.mem_normalizer_iff.mp (hBN₁ hb) x).mp (Subgroup.mem_inf.mp hx).2⟩
    have hpow : ∀ r ∈ (Q ⊔ J₂) ⊓ J₁, r ^ Nat.card Q = 1 := by
      intro r hr
      obtain ⟨hrQJ, hrJ⟩ := Subgroup.mem_inf.mp hr
      have hr' : r ∈ ((Q ⊔ J₂ : Subgroup Γ) : Set Γ) := hrQJ
      rw [Subgroup.coe_mul_of_left_le_normalizer_right Q J₂ hQN] at hr'
      obtain ⟨q, hq, j, hj, rfl⟩ := Set.mem_mul.mp hr'
      have hqe : q = (q * j) * j⁻¹ := by rw [mul_inv_cancel_right]
      have hq1 : q ^ Nat.card Q = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard Q hq)
      rw [hqe, (commute_of_commutator_eq_bot hcomm hrJ (inv_mem hj)).mul_pow] at hq1
      refine hmemJ _ (Subgroup.mem_inf.mpr ⟨pow_mem hrJ _, ?_⟩)
      rw [eq_inv_of_mul_eq_one_left hq1]
      exact inv_mem (pow_mem (inv_mem hj) _)
    have hR3 : Nat.Coprime (Nat.card ((Q ⊔ J₂) ⊓ J₁ : Subgroup Γ)) 3 := by
      refine ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => ?_).symm
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := ((Q ⊔ J₂) ⊓ J₁ : Subgroup Γ)) 3 h3
      have h1 : orderOf (r : Γ) ∣ Nat.card Q := orderOf_dvd_of_pow_eq_one (hpow r r.2)
      rw [Subgroup.orderOf_coe, hr] at h1
      have h2 := Nat.Coprime.coprime_dvd_left h1 (hS3 Q hQ)
      norm_num at h2
    have hR1 := hKL ((Q ⊔ J₂) ⊓ J₁) (inf_le_right.trans hJU) hR3 hBR
    intro q hq
    obtain ⟨j₁, hj₁, j₂, hj₂, hq'⟩ := exists_mul_of_mem_sup hcomm (hsup.symm ▸ hSX Q hQ hq)
    have hj₁R : j₁ ∈ (Q ⊔ J₂) ⊓ J₁ := Subgroup.mem_inf.mpr ⟨by
      rw [eq_mul_inv_of_mul_eq hq']
      exact mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right (inv_mem hj₂)), hj₁⟩
    rw [hR1, Subgroup.mem_bot] at hj₁R
    rw [← hq', hj₁R, one_mul]
    exact hj₂
  apply hJ₁
  rw [eq_bot_iff, ← hinf]
  exact le_inf le_rfl (hJX₁.trans (hXS.trans (sSup_le hQJ)))

end CFSG.RankThree.PartTwo.Sec15.Read148Perf
