module

public import CFSG.Quasithin.Background.D15Chief
public import CFSG.Quasithin.Vol2.Ch9Sec2Z

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits Vol2.Ch10.SecA
open scoped commutatorElement

variable {G : Type} [Group G]

omit [Group G] in
theorem conj_mem_centralizerMod [Group G] {V X U : Subgroup G} {g c : G}
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) (hgU : g ∈ Subgroup.normalizer (U : Set G))
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) (hc : c ∈ centralizerMod V X U) :
    g * c * g⁻¹ ∈ centralizerMod V X U := by
  obtain ⟨hcX, hcV, hcU⟩ := hc
  refine ⟨(Subgroup.mem_normalizer_iff.mp hgX c).mp hcX,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgV hcV) (Subgroup.inv_mem _ hgV), fun u hu => ?_⟩
  have hu' : g⁻¹ * u * g⁻¹⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgU) u).mp hu
  have h1 := (Subgroup.mem_normalizer_iff.mp hgV _).mp (hcU _ hu')
  have e : g * c * g⁻¹ * u * (g * c * g⁻¹)⁻¹ * u⁻¹ =
      g * (c * (g⁻¹ * u * g⁻¹⁻¹) * c⁻¹ * (g⁻¹ * u * g⁻¹⁻¹)⁻¹) * g⁻¹ := by group
  rw [e]
  exact h1

omit [Group G] in
theorem le_normalizer_centralizerMod [Group G] {V X U Y : Subgroup G}
    (hV : Y ≤ Subgroup.normalizer (V : Set G)) (hU : Y ≤ Subgroup.normalizer (U : Set G))
    (hX : Y ≤ Subgroup.normalizer (X : Set G)) :
    Y ≤ Subgroup.normalizer (centralizerMod V X U : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨conj_mem_centralizerMod (hV hg) (hU hg) (hX hg), fun h => ?_⟩
  have := conj_mem_centralizerMod (Subgroup.inv_mem _ (hV hg)) (Subgroup.inv_mem _ (hU hg))
    (Subgroup.inv_mem _ (hX hg)) h
  simpa [mul_assoc] using this

variable [Finite G]

omit [Finite G] in
theorem le_pCoreOf_sup_of_normal {L T X : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hXLT : X ≤ L ⊔ T)
    (hn : L ⊔ T ≤ Subgroup.normalizer (X : Set G)) (hC : IsPGroup 2 ↥(L ⊓ X)) :
    X ≤ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_le_normalizer 2 hXLT hn ?_
  intro x
  obtain ⟨l, hl, t, ht, hx⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTL).mp (hXLT x.2)
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨l', hl', he⟩ := Lem3328.exists_pow_mul (hTL ht) hl (2 ^ k)
  rw [htk, mul_one] at he
  have hxL : (x : G) ^ 2 ^ k ∈ L := by rw [hx, he]; exact hl'
  have hxX : (x : G) ^ 2 ^ k ∈ X := X.pow_mem x.2 _
  obtain ⟨m, hm⟩ := hC ⟨_, Subgroup.mem_inf.mpr ⟨hxL, hxX⟩⟩
  refine ⟨k + m, Subtype.ext ?_⟩
  have := congrArg Subtype.val hm
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
  rw [pow_add, pow_mul]
  exact this

variable {T L I : Subgroup G}

theorem le_pCoreOf_fsuL0_of_normal
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hnn : ¬ T ≤ Subgroup.normalizer (L : Set G)) {X : Subgroup G} (hXL0 : X ≤ fsuL0 T L)
    (hn : fsuL0 T L ≤ Subgroup.normalizer (X : Set G))
    (hT : T ≤ Subgroup.normalizer (X : Set G)) (hL : ¬ L ≤ X) : X ≤ pCoreOf 2 (fsuL0 T L) := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hnn
  obtain ⟨φ, -, hk, hφL, hφLt⟩ := exists_fsuL0_prod_of_fsu h37 h38 hfsu hnn ht htn
  have hloc := hfsu.maximal.1
  have hsL := isSimpleGroup_of_not_normal h37 h38 hfsu.simple hfsu.nonabelian hfsu.qtke
    hfsu.faithful hnn
  have hXL : X ⊓ L ≤ pCoreOf 2 L := by
    set D := X ⊓ L with hDdef
    have hDL : D ≤ L := inf_le_right
    have hDn : L ≤ Subgroup.normalizer (D : Set G) := fun l hl =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hn (le_fsuL0 T L hl), Subgroup.le_normalizer hl⟩
    have : (D.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDL).mpr hDn
    have hnorm := this.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (QuotientGroup.mk'_surjective _)
    rcases hsL.eq_bot_or_eq_top_of_normal ((D.subgroupOf L).map (QuotientGroup.mk' _)) with
      hb | htop
    · intro y hy
      have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨y, hy.2⟩) ∈
          (D.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
        ⟨⟨y, hy.2⟩, hy, rfl⟩
      rw [hb, Subgroup.mem_bot, QuotientGroup.mk'_apply, mk_eq_one_iff] at hmem
      exact hmem
    · exfalso
      apply hL
      have hDeq : D = L := eq_of_forall_mul_mem_pCoreOf hfsu.faithful hDL hDn fun x hx => by
        have hx' : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hx⟩) ∈
            (D.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
          rw [htop]
          exact Subgroup.mem_top _
        obtain ⟨d, hd, hdx⟩ := hx'
        refine ⟨d, hd, ?_⟩
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
          ← subgroupOf_pCoreOf, Subgroup.mem_subgroupOf] at hdx
        simpa using hdx
      rw [← hDeq]
      exact inf_le_left
  have hXLt : X ⊓ CFSG.conjugate L t ≤ pCoreOf 2 (CFSG.conjugate L t) := by
    intro y hy
    have h1 : t * y * t⁻¹ ∈ X ⊓ L :=
      ⟨(Subgroup.mem_normalizer_iff.mp (hT ht) y).mp hy.1,
        Vol2.Ch10.SecA.mem_conjugate_iff.mp hy.2⟩
    rw [pCoreOf_conjugate, Vol2.Ch10.SecA.mem_conjugate_iff]
    exact hXL h1
  intro x hx
  have hxL0 := hXL0 hx
  suffices hφ : φ ⟨x, hxL0⟩ = 1 by
    rw [← MonoidHom.mem_ker, hk, Subgroup.mem_subgroupOf] at hφ
    exact hφ
  have h1 : (φ ⟨x, hxL0⟩).1 ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro c
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective c
    have hlL0 : l ∈ fsuL0 T L := le_fsuL0 T L hl
    have hyL : ⁅x, l⁆ ∈ X ⊓ L := by
      rw [commutatorElement_def]
      refine ⟨?_, ?_⟩
      · rw [show x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) by group]
        exact X.mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hn hlL0) _).mp (X.inv_mem hx))
      · have h2 : x * l * x⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (fsuL0_le_normalizer hloc hxL0) l).mp hl
        exact L.mul_mem h2 (L.inv_mem hl)
    have hval : φ ⟨⁅x, l⁆, le_fsuL0 T L hyL.2⟩ = φ ⁅(⟨x, hxL0⟩ : ↥(fsuL0 T L)), ⟨l, hlL0⟩⁆ := rfl
    rw [hφL _ hyL.2, map_commutatorElement, hφL l hl] at hval
    have h2 := congrArg Prod.fst hval
    rw [(mk_eq_one_iff (⟨_, hyL.2⟩ : ↥L)).mpr (hXL hyL)] at h2
    have h3 : ⁅(φ ⟨x, hxL0⟩).1, ((⟨l, hl⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L)⁆ = 1 := by
      simpa [commutatorElement_def] using h2.symm
    exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
  have h2 : (φ ⟨x, hxL0⟩).2 ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro c
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective c
    have hlL0 : l ∈ fsuL0 T L := conjugate_le_fsuL0 ht hl
    have hyL : ⁅x, l⁆ ∈ X ⊓ CFSG.conjugate L t := by
      rw [commutatorElement_def]
      refine ⟨?_, ?_⟩
      · rw [show x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) by group]
        exact X.mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hn hlL0) _).mp (X.inv_mem hx))
      · have h2 : x * l * x⁻¹ ∈ CFSG.conjugate L t := (Subgroup.mem_normalizer_iff.mp
          (fsuL0_le_normalizer_conjugate hloc (le_fsuM T L ht) hxL0) l).mp hl
        exact (CFSG.conjugate L t).mul_mem h2 ((CFSG.conjugate L t).inv_mem hl)
    have hval : φ ⟨⁅x, l⁆, conjugate_le_fsuL0 ht hyL.2⟩ =
        φ ⁅(⟨x, hxL0⟩ : ↥(fsuL0 T L)), ⟨l, hlL0⟩⁆ := rfl
    rw [hφLt _ hyL.2, map_commutatorElement, hφLt l hl] at hval
    have h2 := congrArg Prod.snd hval
    rw [(mk_eq_one_iff (⟨_, hyL.2⟩ : ↥(CFSG.conjugate L t))).mpr (hXLt hyL)] at h2
    have h3 : ⁅(φ ⟨x, hxL0⟩).2, ((⟨l, hl⟩ : ↥(CFSG.conjugate L t)) :
        ↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t))⁆ = 1 := by
      simpa [commutatorElement_def] using h2.symm
    exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
  rw [center_quot_eq_bot_of_fsu h37 h38 hfsu hnn, Subgroup.mem_bot] at h1
  rw [center_quot_conjugate_eq_bot_of_fsu h37 h38 hfsu hnn ht htn, Subgroup.mem_bot] at h2
  exact Prod.ext h1 h2

theorem relIndex_mul_relIndex_le {U V X : Subgroup G} (hVU : V ≤ U)
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (hUV : U ≤ Subgroup.normalizer (V : Set G)) :
    (V ⊓ Subgroup.centralizer (X : Set G)).relIndex V * (centralizerMod V U X).relIndex U ≤
      (U ⊓ Subgroup.centralizer (X : Set G)).relIndex U := by
  have hVU₁ : V ≤ centralizerMod V U X := fun v hv => ⟨hVU hv, Subgroup.le_normalizer hv,
    fun x hx => by
      rw [show v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) by group]
      exact V.mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hXV hx) _).mp (V.inv_mem hv))⟩
  have hCU₁ : U ⊓ Subgroup.centralizer (X : Set G) ≤ centralizerMod V U X := fun u hu =>
    ⟨hu.1, hUV hu.1, fun x hx => by
      rw [(Subgroup.mem_centralizer_iff.mp hu.2 x hx).symm, mul_inv_cancel_right, mul_inv_cancel]
      exact V.one_mem⟩
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ hCU₁ (centralizerMod_le_left _ _ _)]
  refine Nat.mul_le_mul_right _ ?_
  have e : V ⊓ Subgroup.centralizer (X : Set G) = (U ⊓ Subgroup.centralizer (X : Set G)) ⊓ V := by
    rw [inf_comm (U ⊓ _), ← inf_assoc, inf_eq_left.mpr hVU]
  rw [e, Subgroup.inf_relIndex_right]
  exact Subgroup.relIndex_le_of_le_right hVU₁ (D15Proof.relIndex_ne_zero _ _)

variable {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem centralizerMod_le_Q (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat)
    (hnot : ∃ u ∈ zQ T I, ∃ g ∈ fsuL0 T L, g * u * g⁻¹ * u⁻¹ ∉ fsuV T I) :
    centralizerMod (fsuV T I) (fsuL0 T L ⊔ T) (zQ T I) ≤
      T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
  set C := centralizerMod (fsuV T I) (fsuL0 T L ⊔ T) (zQ T I) with hCdef
  have hCn : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_centralizerMod S.hN S.L0T_le_normalizer_zQ fun x hx => Subgroup.le_normalizer hx
  have hL0C : fsuL0 T L ⊓ C ≤ pCoreOf 2 (fsuL0 T L) := by
    refine le_pCoreOf_fsuL0_of_normal h37c h38c S.hyp.fsu S.not_le_normalizer_L inf_le_left
      (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx, hCn (Subgroup.mem_sup_left hx)⟩)
      (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨T_le_normalizer_L0 hx, hCn (Subgroup.mem_sup_right hx)⟩) fun hLC => ?_
    obtain ⟨u, hu, g, hg, hgu⟩ := hnot
    obtain ⟨t, ht, htn⟩ := S.exists_not_mem_normalizer
    have hLtC : CFSG.conjugate L t ≤ C := fun l hl => by
      have h1 : t * l * t⁻¹ ∈ C := (hLC (Vol2.Ch10.SecA.mem_conjugate_iff.mp hl)).2
      have h2 := (Subgroup.mem_normalizer_iff.mp (hCn (Subgroup.mem_sup_right (T.inv_mem ht)))
        _).mp h1
      simpa [mul_assoc] using h2
    have hL0 : fsuL0 T L ≤ C := by
      rw [fsuL0_eq_sup_of_fsu h37c h38c S.hyp.fsu S.not_le_normalizer_L ht htn]
      exact sup_le (fun l hl => (hLC hl).2) hLtC
    exact hgu ((hL0 hg).2.2 u hu)
  rw [← S.hQ]
  exact le_pCoreOf_sup_of_normal S.hyp.fsu.sylow.1 T_le_normalizer_L0
    (centralizerMod_le_left _ _ _) hCn ((pCoreOf_isPGroup 2 _).to_le hL0C)

end Setup

end CFSG.Quasithin.H13.Ch9
