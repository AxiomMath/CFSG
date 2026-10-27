module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2K
public import CFSG.Quasithin.Vol2.Ch12Sec6T2J
public import CFSG.Quasithin.Vol2.Ch12Sec6T2Stmts
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NNK

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] [IsMulCommutative ↥V] in
theorem false_of_nine_le {A B : Subgroup G} (hA : IsElemAbelian 3 A) (hcA : Nat.card A = 9)
    (hAB : A ≤ B) (hB : IsPGroup 2 ↥B) : False := by
  have : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [hcA]; norm_num)
  have : Nontrivial ↥A := Finite.one_lt_card_iff_nontrivial.1 (by rw [hcA]; norm_num)
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥A)
  obtain ⟨e, he⟩ := hB ⟨a, hAB a.2⟩
  have he' : (a : G) ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  exact ha (Subtype.ext (Sec1211Kv.eq_one_of_two_three he' (hA.2 _ a.2)))

theorem exists_psiLv (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) :
    ∃ f : ↥(Lv L v) →* ↥A6s, Function.Surjective f ∧ IsPGroup 2 ↥f.ker ∧
      ∀ l : ↥(Lv L v),
        (f l : Equiv.Perm (Fin 8)) = psiP F hH (Subgroup.inclusion (Lv_le_L L v) l) := by
  let f : ↥(Lv L v) →* ↥A6s :=
    ((psiP F hH).comp (Subgroup.inclusion (Lv_le_L L v))).codRestrict A6s fun l =>
      psiP_mem_A6s h1222 F hH hv hβ (l := Subgroup.inclusion (Lv_le_L L v) l) l.2
  refine ⟨f, fun a => ?_, fun k => ?_, fun l => rfl⟩
  · obtain ⟨l, hl, hla⟩ := exists_Lv_of_A6s h1222 F hH hv hβ a a.2
    exact ⟨⟨l, hl⟩, Subtype.ext hla⟩
  · have hk : psiP F hH (Subgroup.inclusion (Lv_le_L L v) (k : ↥(Lv L v))) = 1 :=
      congrArg Subtype.val (k.2 : f k = 1)
    have hq : S126L19a.psi F hH (Subgroup.inclusion (Lv_le_L L v) (k : ↥(Lv L v))) = 1 :=
      Subtype.ext hk
    have hC := (S126L19a.psi_eq_one_iff F hH _).1 hq
    obtain ⟨n, hn⟩ :=
      isPGroup_CL h1222 hH ⟨((k : ↥(Lv L v)) : G), Lv_le_L L v (k : ↥(Lv L v)).2, hC⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this

theorem Lv_dichotomy (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {N : Subgroup G}
    (hNL : N ≤ Lv L v) (hNn : Lv L v ≤ Subgroup.normalizer (N : Set G)) :
    N = Lv L v ∨ IsPGroup 2 ↥N := by
  obtain ⟨f, hf, hk, -⟩ := exists_psiLv h1222 F hH hv hβ
  have := isSimpleGroup_A6s
  exact Sec1211Kv.eq_or_isPGroup_of_surjective (perfectCore_perfect _) f hf hk hNL hNn

theorem exists_nine_Lv (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) :
    ∃ A ≤ Lv L v, IsElemAbelian 3 A ∧ Nat.card A = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf, hk, -⟩ := exists_psiLv h1222 F hH hv hβ
  have hk3 : ¬ 3 ∣ Nat.card ↥f.ker := by
    obtain ⟨e, he⟩ := hk.exists_card_eq
    rw [he]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hr : 2 ≤ CFSG.Open.pRank 3 (Lv L v) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
      ← CFSG.SectionRank.pRank_quotient_eq f.ker hk3,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
        (QuotientGroup.quotientKerEquivOfSurjective f hf)]
    exact two_le_pRank_A6s
  obtain ⟨E, hEL, hE, hcE⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (Lv L v)
  have h9 : 3 ^ 2 ∣ Nat.card ↥E := by
    rw [hcE]
    exact Nat.pow_dvd_pow 3 hr
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9
  have hEc := hE.1
  have hK3 : IsElemAbelian 3 K := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x _ => Subtype.ext ?_⟩
    · exact hEc.is_comm.comm (a : ↥E) (b : ↥E)
    · simpa using hE.2 (x : G) x.2
  refine ⟨K.map E.subtype, (Subgroup.map_subtype_le K).trans hEL,
    CFSG.SectionRank.isElemAbelian_map hK3 E.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
  norm_num

theorem eq_one_of_comm_mem (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {N : Subgroup G}
    (hNn : Lv L v ≤ Subgroup.normalizer (N : Set G)) (hN2 : IsPGroup 2 ↥N) {a : G}
    (ha : a ∈ Lv L v) (ha3 : a ^ 3 = 1) (hc : ∀ l ∈ Lv L v, (a * l)⁻¹ * (l * a) ∈ N) :
    a = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLvL := Lv_le_L L v
  set M : Subgroup (Equiv.Perm (Fin 8)) := ((Lv L v ⊓ N).subgroupOf L).map (psiP F hH) with hM
  have hMA : M ≤ A6s := by
    rintro _ ⟨z, hz, rfl⟩
    exact psiP_mem_A6s h1222 F hH hv hβ hz.1
  have hMn : ∀ s ∈ A6s, ∀ m ∈ M, s * m * s⁻¹ ∈ M := by
    intro s hs m hm
    obtain ⟨l, hl, rfl⟩ := exists_Lv_of_A6s h1222 F hH hv hβ s hs
    obtain ⟨z, hz, rfl⟩ := hm
    refine ⟨l * z * l⁻¹, ⟨?_, ?_⟩, by rw [map_mul, map_mul, map_inv]⟩
    · exact (Lv L v).mul_mem ((Lv L v).mul_mem hl hz.1) ((Lv L v).inv_mem hl)
    · exact (Subgroup.mem_normalizer_iff.1 (hNn hl) _).1 hz.2
  have hM2 : IsPGroup 2 ↥M := by
    have h1 : IsPGroup 2 ↥(Lv L v ⊓ N) := hN2.to_le inf_le_right
    have h2 : IsPGroup 2 ↥((Lv L v ⊓ N).subgroupOf L) :=
      h1.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hLvL)).symm
    exact h2.map _
  have hMb := eq_bot_of_normal hMA hMn hM2
  set al : ↥L := ⟨a, hLvL ha⟩ with hal
  have hcomm : ∀ s ∈ A6s, psiP F hH al * s = s * psiP F hH al := by
    intro s hs
    obtain ⟨l, hl, rfl⟩ := exists_Lv_of_A6s h1222 F hH hv hβ s hs
    have hmem : psiP F hH ((al * l)⁻¹ * (l * al)) ∈ M :=
      ⟨(al * l)⁻¹ * (l * al), ⟨(Lv L v).mul_mem ((Lv L v).inv_mem ((Lv L v).mul_mem ha hl))
        ((Lv L v).mul_mem hl ha), hc l hl⟩, rfl⟩
    rw [hMb, Subgroup.mem_bot, map_mul, map_inv, map_mul, map_mul, inv_mul_eq_one] at hmem
    exact hmem
  rcases eq_of_comm hcomm with h1 | h1
  · have hq : S126L19a.psi F hH al = 1 := Subtype.ext h1
    have haC := (S126L19a.psi_eq_one_iff F hH al).1 hq
    obtain ⟨k, hk⟩ := isPGroup_CL h1222 hH ⟨a, hLvL ha, haC⟩
    have hk' : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Sec1211Kv.eq_one_of_two_three hk' ha3
  · exfalso
    have h0 := (mem_A6s.1 (psiP_mem_A6s h1222 F hH hv hβ (l := al) ha)).1
    rw [h1] at h0
    exact absurd h0 (by decide)

theorem pCoreOf_Gv_ne_bot (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) :
    pCoreOf 2 (Gv v) ≠ ⊥ := by
  have hnv : IsNonsing (F.β ⟨v, hv⟩) := hβ ▸ ⟨pe 0 1, rfl, S126L20a.wt_pe (by decide)⟩
  have hv1 : v ≠ 1 := fun h => ne_one_of_nonsing hnv (by
    rw [show (⟨v, hv⟩ : ↥V) = 1 from Subtype.ext h, map_one])
  have hvG : v ∈ Gv v := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hN : Gv v ≤ Subgroup.normalizer (Subgroup.zpowers v : Set G) := by
    intro y hy
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hy).symm k).symm).eq.symm
  have hle : Subgroup.zpowers v ≤ pCoreOf 2 (Gv v) :=
    le_pCoreOf_of_le_normalizer 2 (Subgroup.zpowers_le.mpr hvG) hN
      ((S126L20.isPGroup_V h1222 hH).to_le (Subgroup.zpowers_le.mpr hv))
  intro hbot
  rw [hbot, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  exact hv1 hle

theorem exists_normal_Kv (h1222 : Stmt12_2_2) (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat)
    (hA21 : AsA21SQTKSection) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V)
    (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) :
    ∃ Kv ∈ cComp (Gv v), Lv L v ≤ Kv ∧ Gv v ≤ Subgroup.normalizer (Kv : Set G) := by
  set H := Gv v with hHdef
  have hyp := hH.hyp
  have : IsSimpleGroup G := hyp.simple
  have hqtke : QuasithinUnique.QTKECore G :=
    QuasithinUnique.qtkeCore_of_cat hyp.nonabelian hyp.qtke
  have hH2 : pCoreOf 2 H ≠ ⊥ := pCoreOf_Gv_ne_bot h1222 F hH hv hβ
  have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian hH2
  have h121 : cCompSpan H = perfectCore H :=
    QuasithinUnique.Vol2Native.lemma_1_2_1_one hqtke.1 h39 hH2
  have hLvH : Lv L v ≤ H := Lv_le_Gv L v
  have hLvp : ⁅Lv L v, Lv L v⁆ = Lv L v := perfectCore_perfect _
  have hLvE : Lv L v ≤ cCompSpan H := h121 ▸ le_perfectCore_of_perfect hLvH hLvp
  set B := (Lv L v).subgroupOf H with hBdef
  have hBmap : B.map H.subtype = Lv L v := Subgroup.map_subgroupOf_eq_of_le hLvH
  have hBp : ⁅B, B⁆ = B := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, hBmap, hLvp]
  have hspan : cCompSpan H ≤ (cCompSpan (⊤ : Subgroup ↥H)).map H.subtype := by
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp hK)]
    exact Subgroup.map_mono (le_cCompSpan (subgroupOf_mem_cComp hK))
  have hBE : B ≤ cCompSpan (⊤ : Subgroup ↥H) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hspan (hLvE hx)
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  have hBn : ∀ N : Subgroup ↥H, N ≤ B → B ≤ Subgroup.normalizer (N : Set ↥H) →
      N = B ∨ IsPGroup 2 ↥N := by
    intro N hNB hNn
    have hN'B : N.map H.subtype ≤ Lv L v := hBmap ▸ Subgroup.map_mono hNB
    have hN'n : Lv L v ≤ Subgroup.normalizer ((N.map H.subtype : Subgroup G) : Set G) := by
      intro l hl
      have hlB : (⟨l, hLvH hl⟩ : ↥H) ∈ B := hl
      have h1 := hNn hlB
      rw [Subgroup.mem_normalizer_iff] at h1 ⊢
      intro g
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨_, (h1 x).mp hx, rfl⟩
      · rintro ⟨y, hy, hyg⟩
        have hgH : g ∈ H := by
          have : l⁻¹ * (l * g * l⁻¹) * l ∈ H :=
            H.mul_mem (H.mul_mem (H.inv_mem (hLvH hl)) (hyg ▸ y.2)) (hLvH hl)
          simpa [mul_assoc] using this
        refine ⟨⟨g, hgH⟩, (h1 ⟨g, hgH⟩).mpr ?_, rfl⟩
        have : (⟨l, hLvH hl⟩ * ⟨g, hgH⟩ * (⟨l, hLvH hl⟩ : ↥H)⁻¹ : ↥H) = y :=
          Subtype.ext hyg.symm
        rw [this]
        exact hy
    rcases Lv_dichotomy h1222 F hH hv hβ hN'B hN'n with h | h
    · left
      apply Subgroup.map_injective H.subtype_injective
      rw [h, hBmap]
    · right
      exact h.of_injective (Subgroup.equivMapOfInjective N H.subtype
        H.subtype_injective).toMonoidHom (Subgroup.equivMapOfInjective N H.subtype
        H.subtype_injective).injective
  obtain ⟨A, hALv, hA, hcA⟩ := exists_nine_Lv h1222 F hH hv hβ
  have hAH : A ≤ H := hALv.trans hLvH
  have hAmap : (A.subgroupOf H).map H.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAH
  have hA'B : A.subgroupOf H ≤ B := fun x hx => hALv hx
  have hcA' : Nat.card ↥(A.subgroupOf H) = 9 := by
    have h1 : Nat.card ↥((A.subgroupOf H).map H.subtype) = Nat.card ↥(A.subgroupOf H) :=
      Subgroup.card_map_of_injective H.subtype_injective
    rw [hAmap] at h1
    rw [← h1, hcA]
  have hA' : IsElemAbelian 3 (A.subgroupOf H) := by
    have hAc := hA.1
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · show ((a : ↥H) : G) * ((b : ↥H) : G) = ((b : ↥H) : G) * ((a : ↥H) : G)
      exact congrArg Subtype.val (hAc.is_comm.comm ⟨((a : ↥H) : G), a.2⟩ ⟨((b : ↥H) : G), b.2⟩)
    · simpa using hA.2 (x : G) hx
  obtain ⟨K, hK, hBK, hKn⟩ := Sec1211Kv.exists_normal_cComp_ge hA21 hSQ hBp hBE hBn hA'B hA' hcA'
  have hKnorm : K.Normal := Subgroup.normalizer_eq_top_iff.mp hKn
  refine ⟨K.map H.subtype, map_subtype_mem_cComp hK, ?_, fun h hh => ?_⟩
  · rw [← hBmap]
    exact Subgroup.map_mono hBK
  · rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨_, hKnorm.conj_mem k hk ⟨h, hh⟩, rfl⟩
    · rintro ⟨k, hk, hkg⟩
      have hgH : g ∈ H := by
        have : h⁻¹ * (h * g * h⁻¹) * h ∈ H :=
          H.mul_mem (H.mul_mem (H.inv_mem hh) (hkg ▸ k.2)) hh
        simpa [mul_assoc] using this
      refine ⟨⟨g, hgH⟩, ?_, rfl⟩
      have h1 := hKnorm.conj_mem k hk (⟨h, hh⟩ : ↥H)⁻¹
      have hkg' : (k : G) = h * g * h⁻¹ := hkg
      have e : ((⟨h, hh⟩ : ↥H)⁻¹ * k * ((⟨h, hh⟩ : ↥H)⁻¹)⁻¹ : ↥H) = ⟨g, hgH⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv, inv_inv]
        rw [hkg']
        group
      rwa [e] at h1

theorem false_of_map_sl2 (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {X : Type*} [Group X]
    (φ : ↥(Lv L v) →* X) (hφ : IsPGroup 2 ↥φ.ker) {N : Subgroup X} [Group.IsSolvable ↥N]
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (ψ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (hψ : ψ.ker = N) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hALv, hA, hcA⟩ := exists_nine_Lv h1222 F hH hv hβ
  have h21 : ∀ x : ↥(Lv L v), x ∈ φ.ker → (x : G) ∈ A → (x : G) = 1 := by
    intro x hx hxA
    obtain ⟨e, he⟩ := hφ ⟨x, hx⟩
    have he' : (x : G) ^ 2 ^ e = 1 := by
      simpa using congrArg (fun z : ↥φ.ker => ((z : ↥(Lv L v)) : G)) he
    exact Sec1211Kv.eq_one_of_two_three he' (hA.2 _ hxA)
  set Φ := ψ.comp φ with hΦ
  set K₀ : Subgroup G := Φ.ker.map (Lv L v).subtype with hK₀
  have hK₀L : K₀ ≤ Lv L v := Subgroup.map_subtype_le _
  have hK₀n : Lv L v ≤ Subgroup.normalizer (K₀ : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨l, hl⟩ * k * ⟨l, hl⟩⁻¹, (Φ.normal_ker).conj_mem k hk _, rfl⟩
    · rintro ⟨k, hk, hkg⟩
      have hg : g ∈ Lv L v := by
        have : l⁻¹ * (l * g * l⁻¹) * l ∈ Lv L v :=
          (Lv L v).mul_mem ((Lv L v).mul_mem ((Lv L v).inv_mem hl) (hkg ▸ k.2)) hl
        simpa [mul_assoc] using this
      refine ⟨⟨g, hg⟩, ?_, rfl⟩
      have h1 := (Φ.normal_ker).conj_mem k hk (⟨l, hl⟩ : ↥(Lv L v))⁻¹
      have hkg' : (k : G) = l * g * l⁻¹ := hkg
      have e : ((⟨l, hl⟩ : ↥(Lv L v))⁻¹ * k * ((⟨l, hl⟩ : ↥(Lv L v))⁻¹)⁻¹ : ↥(Lv L v)) =
          ⟨g, hg⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv, inv_inv]
        rw [hkg']
        group
      rwa [e] at h1
  have hAne : ∃ a : ↥A, a ≠ 1 := by
    have : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [hcA]; norm_num)
    have : Nontrivial ↥A := Finite.one_lt_card_iff_nontrivial.1 (by rw [hcA]; norm_num)
    exact exists_ne 1
  rcases Lv_dichotomy h1222 F hH hv hβ hK₀L hK₀n with h | h
  ·
    have hR : φ.range ≤ N := by
      rintro _ ⟨l, rfl⟩
      have hl : (l : G) ∈ K₀ := by rw [h]; exact l.2
      obtain ⟨k, hk, hkl⟩ := hl
      have : k = l := Subtype.ext hkl
      rw [this] at hk
      rw [← hψ]
      exact hk
    have htop : ⁅(⊤ : Subgroup ↥(Lv L v)), (⊤ : Subgroup ↥(Lv L v))⁆ = ⊤ := by
      apply Subgroup.map_injective (Lv L v).subtype_injective
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact perfectCore_perfect _
    have hRp : ⁅φ.range, φ.range⁆ = φ.range := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]
    have : Group.IsSolvable ↥φ.range :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hR)
        (Subgroup.inclusion_injective hR)
    have hR1 := CFSG.LieType.SteinbergBR.eq_bot_of_perfect_of_isSolvable hRp
    obtain ⟨a, ha⟩ := hAne
    apply ha
    have hφa : φ (Subgroup.inclusion hALv a) = 1 := by
      have : φ (Subgroup.inclusion hALv a) ∈ φ.range := ⟨_, rfl⟩
      rwa [hR1, Subgroup.mem_bot] at this
    exact Subtype.ext (h21 _ hφa a.2)
  ·
    have h3 : (3 : ZMod p) ≠ 0 := by
      intro h0
      have h1 : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
      rw [ZMod.natCast_eq_zero_iff] at h1
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h1)
    refine false_of_elemAbelian_nine h3 hA hcA (Φ.comp (Subgroup.inclusion hALv)) fun a ha => ?_
    have hmem : (a : G) ∈ K₀ := ⟨Subgroup.inclusion hALv a, ha, rfl⟩
    obtain ⟨e, he⟩ := h ⟨a, hmem⟩
    have he' : (a : G) ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    exact Subtype.ext (Sec1211Kv.eq_one_of_two_three he' (hA.2 _ a.2))

theorem isQuasisimple_Kv (h1222 : Stmt12_2_2)
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    {Kv : Subgroup G} (hK : Kv ∈ cComp (Gv v)) (hLK : Lv L v ≤ Kv) :
    CFSG.IsQuasisimple (↥Kv ⧸ CFSG.pCore 2 ↥Kv) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Gv v with hHdef
  have hyp := hH.hyp
  have : IsSimpleGroup G := hyp.simple
  have hqtke : QuasithinUnique.QTKECore G :=
    QuasithinUnique.qtkeCore_of_cat hyp.nonabelian hyp.qtke
  have hH2 : pCoreOf 2 H ≠ ⊥ := pCoreOf_Gv_ne_bot h1222 F hH hv hβ
  obtain ⟨hcases, -, -⟩ := QuasithinUnique.Vol2Native.lemma_1_2_1_four_core hqtke.1 h36 hH2 hK
  obtain ⟨ψ, hψs, hψk⟩ := exists_modO2_surjection hK
  let eX : ↥Kv ⧸ CFSG.pCore 2 ↥Kv ≃* ↥(modO2Image H Kv) :=
    (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  have hLvH : Lv L v ≤ H := Lv_le_Gv L v
  let φ : ↥(Lv L v) →* ↥(modO2Image H Kv) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hLvH)).codRestrict
      (modO2Image H Kv) fun l => ⟨Subgroup.inclusion hLvH l, hLK l.2, rfl⟩
  have hφ : IsPGroup 2 ↥φ.ker := by
    intro k
    have hk : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (Subgroup.inclusion hLvH (k : ↥(Lv L v))) =
        1 := congrArg Subtype.val (k.2 : φ k = 1)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 ↥(CFSG.pCore 2 ↥H)) ⟨_, hk⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : ↥(CFSG.pCore 2 ↥H) => ((z : ↥H) : G)) hn
    simpa using this
  rcases hcases with hcomp | h3 | h4
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eX.symm hcomp.1
  · exfalso
    obtain ⟨p, hp, hp3, -, -, -, ψ₃, -, hψ₃k, -⟩ := h3
    exact false_of_map_sl2 h1222 F hH hv hβ φ hφ hp (by omega) ψ₃ hψ₃k
  · exfalso
    obtain ⟨-, -, ⟨e5⟩, -⟩ := h4
    let ψ₄ := e5.toMonoidHom.comp
      (QuotientGroup.mk' (CFSG.fittingSubgroup ↥(modO2Image H Kv)))
    have hψ₄k : ψ₄.ker = CFSG.fittingSubgroup ↥(modO2Image H Kv) := by
      ext x
      simp [ψ₄]
    exact false_of_map_sl2 h1222 F hH hv hβ φ hφ Nat.prime_five (by norm_num) ψ₄ hψ₄k

theorem not_three_dvd_of_ne (h1222 : Stmt12_2_2) (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V)
    (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {Kv K' : Subgroup G}
    (hK : Kv ∈ cComp (Gv v)) (hLK : Lv L v ≤ Kv) (hK' : K' ∈ cComp (Gv v)) (hne : Kv ≠ K') :
    ¬ 3 ∣ Nat.card K' := by
  classical
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Gv v with hHdef
  have hyp := hH.hyp
  have : IsSimpleGroup G := hyp.simple
  have hqtke : QuasithinUnique.QTKECore G :=
    QuasithinUnique.qtkeCore_of_cat hyp.nonabelian hyp.qtke
  have hH2 : pCoreOf 2 H ≠ ⊥ := pCoreOf_Gv_ne_bot h1222 F hH hv hβ
  have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian hH2
  obtain ⟨hc, hcO⟩ := QuasithinUnique.Vol2Native.lemma_1_2_1_two hqtke.1 h37 hH2 hK hK' hne
  have hcomm : ⁅Kv, K'⁆ ≤ pCoreOf 2 H := hc.trans hcO
  have hKH : Kv ≤ H := le_of_mem_cComp hK
  have hK'H : K' ≤ H := le_of_mem_cComp hK'
  have hLvH : Lv L v ≤ H := Lv_le_Gv L v
  set O := CFSG.pCore 2 ↥H with hOdef
  have hO2 : IsPGroup 2 ↥O := CFSG.pCore_isPGroup
  have hP : O.map H.subtype = pCoreOf 2 H := by
    rw [hOdef]; rfl
  have hmemO : ∀ z : ↥H, z ∈ O ↔ (z : G) ∈ pCoreOf 2 H := by
    intro z
    rw [← hP]
    constructor
    · intro hz; exact ⟨z, hz, rfl⟩
    · rintro ⟨w, hw, hwz⟩
      rwa [show w = z from Subtype.ext hwz] at hw
  have hO3 : ¬ 3 ∣ Nat.card ↥O := by
    obtain ⟨e, he⟩ := hO2.exists_card_eq
    rw [he]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  set q := QuotientGroup.mk' O with hq
  have hqeq : ∀ a b : ↥H, q a = q b ↔ ((a⁻¹ * b : ↥H) : G) ∈ pCoreOf 2 H := by
    intro a b
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hmemO]
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥K') 3 h3
  have hyK' : (y : G) ∈ K' := y.2
  have hy3 : (y : G) ^ 3 = 1 := by
    rw [← Subgroup.orderOf_coe] at hy
    rw [← hy]
    exact pow_orderOf_eq_one _
  set yb : ↥H ⧸ O := q ⟨y, hK'H hyK'⟩ with hyb
  have hyc : ∀ k (hk : k ∈ Kv), q ⟨k, hKH hk⟩ * yb = yb * q ⟨k, hKH hk⟩ := by
    intro k hk
    rw [hyb, ← map_mul, ← map_mul, hqeq]
    have h1 := Subgroup.commutator_mem_commutator (K'.inv_mem hyK') (Kv.inv_mem hk)
    rw [commutatorElement_def, inv_inv, inv_inv, Subgroup.commutator_comm] at h1
    have h2 := hcomm h1
    convert h2 using 1
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev]
    group
  have hzc : ∀ z ∈ Subgroup.zpowers yb, ∀ k (hk : k ∈ Kv),
      q ⟨k, hKH hk⟩ * z = z * q ⟨k, hKH hk⟩ := by
    intro z hz k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_right (hyc k hk) n).eq
  have hyb1 : yb ≠ 1 := by
    intro h1
    have h2 : q ⟨y, hK'H hyK'⟩ = q 1 := by rw [← hyb, h1, map_one]
    rw [hqeq] at h2
    have h3' : ((⟨y, hK'H hyK'⟩ : ↥H)⁻¹ * 1 : ↥H) = (⟨y, hK'H hyK'⟩ : ↥H)⁻¹ := mul_one _
    rw [h3'] at h2
    obtain ⟨e, he⟩ := (pCoreOf_isPGroup 2 H) ⟨_, h2⟩
    have he' : ((y : G)⁻¹) ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    have h4 : (y : G)⁻¹ = 1 :=
      Sec1211Kv.eq_one_of_two_three he' (by rw [inv_pow, hy3, inv_one])
    have h5 : (y : G) = 1 := inv_eq_one.mp h4
    have : orderOf (y : G) = 1 := by rw [h5, orderOf_one]
    rw [Subgroup.orderOf_coe, hy] at this
    omega
  have hord : orderOf yb = 3 := by
    refine orderOf_eq_prime ?_ hyb1
    rw [hyb, ← map_pow]
    have : (⟨y, hK'H hyK'⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  obtain ⟨A, hALv, hA, hcA⟩ := exists_nine_Lv h1222 F hH hv hβ
  have hAH : A ≤ H := hALv.trans hLvH
  let α : ↥A →* ↥H ⧸ O := q.comp (Subgroup.inclusion hAH)
  have hαβ : ∀ (a : ↥A) (z : ↥(Subgroup.zpowers yb)),
      Commute (α a) ((Subgroup.zpowers yb).subtype z) := by
    intro a z
    exact hzc z z.2 (a : G) (hLK (hALv a.2))
  let Φ := α.noncommCoprod (Subgroup.zpowers yb).subtype hαβ
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, z⟩ h1
    simp only [Φ, MonoidHom.noncommCoprod_apply] at h1
    have hαz : α a = ((z : ↥H ⧸ O))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hzinv : ((z : ↥H ⧸ O))⁻¹ ∈ Subgroup.zpowers yb := (Subgroup.zpowers yb).inv_mem z.2
    have hac : ∀ l ∈ Lv L v, ((a : G) * l)⁻¹ * (l * a) ∈ pCoreOf 2 H := by
      intro l hl
      have h2 := hzc _ hzinv l (hLK hl)
      rw [← hαz] at h2
      have h3 : q (⟨a, hAH a.2⟩ * ⟨l, hKH (hLK hl)⟩) = q (⟨l, hKH (hLK hl)⟩ * ⟨a, hAH a.2⟩) := by
        rw [map_mul, map_mul]
        exact h2.symm
      rw [hqeq] at h3
      simpa using h3
    have ha1 : (a : G) = 1 :=
      eq_one_of_comm_mem h1222 F hH hv hβ (fun l hl => le_normalizer_pCoreOf 2 H (hLvH hl))
        (pCoreOf_isPGroup 2 H) (hALv a.2) (hA.2 _ a.2) hac
    have ha1' : a = 1 := Subtype.ext ha1
    subst ha1'
    have hz1 : (z : ↥H ⧸ O) = 1 := by
      rw [map_one, one_mul] at h1
      exact h1
    exact Prod.ext rfl (Subtype.ext hz1)
  have hcomm3 : ∀ x y : ↥A × ↥(Subgroup.zpowers yb), x * y = y * x := by
    rintro ⟨a, z⟩ ⟨a', z'⟩
    refine Prod.ext (hA.1.is_comm.comm a a') ?_
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp z.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp z'.2
    apply Subtype.ext
    show (z : ↥H ⧸ O) * z' = z' * z
    rw [← hm, ← hn]
    exact (Commute.zpow_zpow_self yb m n).eq
  have hpow3 : ∀ x : ↥A × ↥(Subgroup.zpowers yb), x ^ 3 = 1 := by
    rintro ⟨a, z⟩
    refine Prod.ext (Subtype.ext (by simpa using hA.2 _ a.2)) ?_
    have hc3 : Nat.card ↥(Subgroup.zpowers yb) = 3 := by rw [Nat.card_zpowers, hord]
    show z ^ 3 = 1
    rw [← hc3]
    exact pow_card_eq_one'
  have h27 : Nat.card (↥A × ↥(Subgroup.zpowers yb)) = 3 ^ 3 := by
    rw [Nat.card_prod, hcA, Nat.card_zpowers, hord]
    norm_num
  have hrk := CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) hcomm3 hpow3 h27 Φ
    hinj (H := ⊤) le_top
  rw [CFSG.SectionRank.pRank_quotient_eq O hO3] at hrk
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥H) ≤ 2 := hSQ.1 3 Nat.prime_three (by norm_num)
  omega

omit [Finite G] in
theorem le_normalizer_oThreePrimeResidual {X Y : Subgroup G}
    (h : Y ≤ Subgroup.normalizer (X : Set G)) :
    Y ≤ Subgroup.normalizer (oThreePrimeResidual X : Set G) := by
  have key : ∀ g ∈ Y, ∀ x ∈ oThreePrimeResidual X, g * x * g⁻¹ ∈ oThreePrimeResidual X := by
    intro g hg x hx
    have hle : oThreePrimeResidual X ≤
        (oThreePrimeResidual X).comap (MulAut.conj g).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr fun z hz => ?_
      obtain ⟨hzX, k, hk⟩ := hz
      show (MulAut.conj g) z ∈ oThreePrimeResidual X
      rw [MulAut.conj_apply]
      apply Subgroup.subset_closure
      exact ⟨(Subgroup.mem_normalizer_iff.mp (h hg) z).mp hzX, k, by
        rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
    exact hle hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have := key g⁻¹ (Y.inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem eq_oThreePrimeResidual (h1222 : Stmt12_2_2)
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    {Kv : Subgroup G} (hK : Kv ∈ cComp (Gv v)) (hLK : Lv L v ≤ Kv)
    (hKn : Gv v ≤ Subgroup.normalizer (Kv : Set G)) :
    Kv = oThreePrimeResidual (perfectCore (Gv v)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := Gv v with hHdef
  set P := perfectCore H with hPdef
  set N := oThreePrimeResidual P with hNdef
  have hyp := hH.hyp
  have : IsSimpleGroup G := hyp.simple
  have hqtke : QuasithinUnique.QTKECore G :=
    QuasithinUnique.qtkeCore_of_cat hyp.nonabelian hyp.qtke
  have hH2 : pCoreOf 2 H ≠ ⊥ := pCoreOf_Gv_ne_bot h1222 F hH hv hβ
  have h121 : cCompSpan H = P := QuasithinUnique.Vol2Native.lemma_1_2_1_one hqtke.1 h39 hH2
  have hKH : Kv ≤ H := le_of_mem_cComp hK
  have hLvH : Lv L v ≤ H := Lv_le_Gv L v
  have hHP : H ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore H)
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := le_normalizer_oThreePrimeResidual hHP
  obtain ⟨A, hALv, hA, hcA⟩ := exists_nine_Lv h1222 F hH hv hβ
  have hKP : Kv ≤ P := h121 ▸ le_cCompSpan hK
  apply le_antisymm
  ·
    have hLvP : Lv L v ≤ P := hLK.trans hKP
    have hLvN : Lv L v ≤ N := by
      have hn : Lv L v ≤ Subgroup.normalizer ((Lv L v ⊓ N : Subgroup G) : Set G) := fun l hl =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl, hHN (hLvH hl)⟩
      have hAN : A ≤ Lv L v ⊓ N := fun a ha =>
        ⟨hALv ha, Subgroup.subset_closure ⟨hLvP (hALv ha), 1, by simpa using hA.2 a ha⟩⟩
      rcases Lv_dichotomy h1222 F hH hv hβ inf_le_left hn with h | h
      · rw [← h]
        exact inf_le_right
      · exact (false_of_nine_le hA hcA hAN h).elim
    set M := Kv ⊓ N with hMdef
    have hLvM : Lv L v ≤ M := le_inf hLK hLvN
    have hMH : M ≤ H := inf_le_left.trans hKH
    have hHM : H ≤ Subgroup.normalizer (M : Set G) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hKn hg, hHN hg⟩
    have hC : perfectCore M ≤ Kv := (perfectCore_le M).trans inf_le_left
    have hLvC : Lv L v ≤ perfectCore M := le_perfectCore_of_perfect hLvM (perfectCore_perfect _)
    have hCne : perfectCore M ≠ ⊥ := fun h0 =>
      false_of_nine_le hA hcA (hALv.trans (hLvC.trans h0.le)) IsPGroup.of_bot
    have hCH : perfectCore M ≤ H := (perfectCore_le M).trans hMH
    have hCsub : IsSubnormal (perfectCore M) H :=
      IsSubnormal.step hCH ((Subgroup.normal_subgroupOf_iff_le_normalizer hCH).2
        (hHM.trans (normalizer_le_normalizer_perfectCore M))) (IsSubnormal.refl H)
    have hCeq : perfectCore M = Kv := by
      by_contra hne
      exact not_subnormal_of_mem_cComp hK (lt_of_le_of_ne hC hne) hCne (perfectCore_perfect _)
        hCsub
    calc Kv = perfectCore M := hCeq.symm
      _ ≤ M := perfectCore_le M
      _ ≤ N := inf_le_right
  ·
    set 𝒮 : Set (Subgroup G) := {K' | K' ∈ cComp H ∧ K' ≠ Kv} with h𝒮
    have hPeq : P = Kv ⊔ sSup 𝒮 := by
      rw [← h121]
      apply le_antisymm
      · refine sSup_le fun K' hK' => ?_
        by_cases h : K' = Kv
        · rw [h]
          exact le_sup_left
        · exact le_sup_of_le_right (le_sSup ⟨hK', h⟩)
      · exact sup_le (le_cCompSpan hK) (sSup_le fun K' hK' => le_cCompSpan hK'.1)
    have hcop : Nat.Coprime 3 (Nat.card ↥(sSup 𝒮)) := by
      refine coprime_card_sSup (fun K' hK' => sSup_le fun K'' hK'' =>
        CFSG.Quasithin.le_normalizer_of_mem_cComp hK'.1 hK''.1) fun K' hK' => ?_
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
        (not_three_dvd_of_ne h1222 h37 F hH hv hβ hK hLK hK'.1 (Ne.symm hK'.2))
    have hSn : sSup 𝒮 ≤ Subgroup.normalizer (Kv : Set G) :=
      (sSup_le fun K' hK' => le_of_mem_cComp hK'.1).trans hKn
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    obtain ⟨hxP, k, hk⟩ := hx
    rw [hPeq] at hxP
    exact mem_of_pow_three hSn hcop hxP hk

end S126T2

theorem lemma12_6_3_of (h1222 : Stmt12_2_2)
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat)
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (hA21 : AsA21SQTKSection) :
    Lemma12_6_3 := by
  intro G _ _ T L V _ F hH v hv hβ
  obtain ⟨Kv, hK, hLK, hKn⟩ := exists_normal_Kv h1222 h39 hA21 F hH hv hβ
  exact ⟨Kv, hK, hLK, eq_oThreePrimeResidual h1222 h37 h39 F hH hv hβ hK hLK hKn, hKn,
    isQuasisimple_Kv h1222 h36 F hH hv hβ hK hLK⟩

end CFSG.Quasithin.H13
