module

public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {V H E J : Subgroup G}

theorem commConjSup_le_centralizer (V H E : Subgroup G) :
    commConjSup V H E ≤ Subgroup.centralizer (V : Set G) := by
  rw [commConjSup]
  refine iSup_le fun k => iSup_le fun _hk => iSup_le fun hcomm => ?_
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact hcomm a ha x hx

theorem SevenNineConfig.barSub_eq_zpowers (h : Hyp73 V H E J) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) J φ) {L : Subgroup X} {p : ℕ}
    {Yb Zb : Subgroup X} (hc : SevenNineConfig L (barSub (kSub V H E) φ V) p Yb Zb) {v : G}
    (hvV : v ∈ V) (hvJ : v ∉ J) :
    barSub (kSub V H E) φ V = Subgroup.zpowers (φ ⟨v, le_kSub h.mem hvV⟩) := by
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  have htV : φ ⟨v, le_kSub h.mem hvV⟩ ∈ barSub (kSub V H E) φ V :=
    mem_barSub.mpr ⟨⟨v, le_kSub h.mem hvV⟩, hvV, rfl⟩
  have ht1 : φ ⟨v, le_kSub h.mem hvV⟩ ≠ 1 := by
    intro h1
    exact hvJ ((hφ.ker_iff ⟨v, le_kSub h.mem hvV⟩).mp h1)
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr htV) ?_).symm
  rw [hc.card_s]
  have hlt : 1 < Nat.card (Subgroup.zpowers (φ ⟨v, le_kSub h.mem hvV⟩)) := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro hbot
    exact ht1 (Subgroup.zpowers_eq_bot.mp hbot)
  omega

theorem SevenNineCompl.barSub_eq {X : Type} [Group X] {φ : ↥(kSub V H E) →* X}
    (hφ : IsBarMap (kSub V H E) J φ) {Yb : Subgroup X} {v : G} {P : Subgroup G}
    (hP : SevenNineCompl (kSub V H E) J φ Yb v P) :
    barSub (kSub V H E) φ P = Yb := by
  let K := kSub V H E
  let Y := barPre K φ Yb
  change barSub K φ P = Yb
  have hPK : P ≤ K := hP.le.trans (barPre_le K φ Yb)
  have hYK : Y ⊓ J ≤ K := inf_le_left.trans (barPre_le K φ Yb)
  have hY : Y = P ⊔ (Y ⊓ J) := hP.sup_eq.symm
  have hbot : barSub K φ (Y ⊓ J) = ⊥ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := mem_barSub.mp hx
      have hker : φ k = 1 := (hφ.ker_iff k).mpr (Subgroup.mem_inf.mp hk).2
      rw [hker]
      exact Subgroup.one_mem (⊥ : Subgroup X)
    · exact bot_le
  have hYP : barSub K φ Y = barSub K φ P := by
    rw [hY, barSub_sup hPK hYK φ, hbot, sup_bot_eq]
  calc barSub K φ P = barSub K φ Y := hYP.symm
    _ = Yb := barSub_barPre hφ Yb

theorem SevenNineCompl.injective {X : Type} [Group X] {φ : ↥(kSub V H E) →* X}
    (hφ : IsBarMap (kSub V H E) J φ) {Yb : Subgroup X} {v : G} {P : Subgroup G}
    (hP : SevenNineCompl (kSub V H E) J φ Yb v P) {x y : ↥(kSub V H E)} (hx : (x : G) ∈ P)
    (hy : (y : G) ∈ P) (hxy : φ x = φ y) : x = y := by
  have hphi : φ (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, ← hxy, inv_mul_cancel]
  have hJ : ((x⁻¹ * y : ↥(kSub V H E)) : G) ∈ J := (hφ.ker_iff (x⁻¹ * y)).mp hphi
  have hPmem : ((x⁻¹ * y : ↥(kSub V H E)) : G) ∈ P := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact P.mul_mem (P.inv_mem hx) hy
  have hYmem : ((x⁻¹ * y : ↥(kSub V H E)) : G) ∈ barPre (kSub V H E) φ Yb :=
    hP.le hPmem
  have hbot : ((x⁻¹ * y : ↥(kSub V H E)) : G) ∈ (⊥ : Subgroup G) := by
    rw [← hP.inf_eq]
    exact ⟨hPmem, hYmem, hJ⟩
  have hone : ((x⁻¹ * y : ↥(kSub V H E)) : G) = 1 := Subgroup.mem_bot.mp hbot
  have hxy' : (x : G)⁻¹ * (y : G) = 1 := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hone
  exact Subtype.ext (inv_mul_eq_one.mp hxy')

theorem SevenNineCompl.card_barSub_of_le {X : Type} [Group X] {φ : ↥(kSub V H E) →* X}
    (hφ : IsBarMap (kSub V H E) J φ) {Yb : Subgroup X} {v : G} {P : Subgroup G}
    (hP : SevenNineCompl (kSub V H E) J φ Yb v P) {A : Subgroup G} (hA : A ≤ P) :
    Nat.card (barSub (kSub V H E) φ A) = Nat.card A := by
  let K := kSub V H E
  let Y := barPre K φ Yb
  change Nat.card (barSub K φ A) = Nat.card A
  have hAK : A ≤ K := hA.trans (hP.le.trans (barPre_le K φ Yb))
  have hφ' : IsBarMap K (K ⊓ J) φ :=
    ⟨hφ.surjective, fun k => (hφ.ker_iff k).trans
      ⟨fun hk => ⟨k.2, hk⟩, fun hk => hk.2⟩⟩
  have hcard := card_barSub_eq_relIndex_of_isBarMap (K := K) (N := K ⊓ J) (A := A)
    hAK inf_le_left hφ'
  rw [hcard]
  have hbot : (K ⊓ J) ⊓ A = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ P ⊓ (Y ⊓ J) := by
        obtain ⟨hxKJ, hxA⟩ := Subgroup.mem_inf.mp hx
        exact ⟨hA hxA, hP.le (hA hxA), (Subgroup.mem_inf.mp hxKJ).2⟩
      exact hP.inf_eq ▸ hx'
    · exact bot_le
  calc (K ⊓ J).relIndex A = ((K ⊓ J) ⊓ A).relIndex A :=
        (Subgroup.inf_relIndex_right (H := K ⊓ J) (K := A)).symm
    _ = (⊥ : Subgroup G).relIndex A := by rw [hbot]
    _ = Nat.card A := Subgroup.relIndex_bot_left A

theorem SevenNineCompl.isElemAbelian {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) J φ) {L : Subgroup X} {p : ℕ}
    {Yb Zb : Subgroup X} (hc : SevenNineConfig L (barSub (kSub V H E) φ V) p Yb Zb) {v : G}
    {P : Subgroup G} (hP : SevenNineCompl (kSub V H E) J φ Yb v P) : IsElemAbelian p P := by
  let K := kSub V H E
  have hPK : P ≤ K := hP.le.trans (barPre_le K φ Yb)
  have hbar : barSub K φ P = Yb := SevenNineCompl.barSub_eq hφ hP
  have key : ∀ a b : ↥P,
      φ (⟨(a : G), hPK a.2⟩ : ↥K) * φ (⟨(b : G), hPK b.2⟩ : ↥K) =
        φ (⟨(b : G), hPK b.2⟩ : ↥K) * φ (⟨(a : G), hPK a.2⟩ : ↥K) := by
    intro a b
    have haY : φ (⟨(a : G), hPK a.2⟩ : ↥K) ∈ Yb := by
      rw [← hbar]
      exact mem_barSub.mpr ⟨⟨(a : G), hPK a.2⟩, a.2, rfl⟩
    have hbY : φ (⟨(b : G), hPK b.2⟩ : ↥K) ∈ Yb := by
      rw [← hbar]
      exact mem_barSub.mpr ⟨⟨(b : G), hPK b.2⟩, b.2, rfl⟩
    have hcomm := hc.elemAbelian.1.is_comm.comm ⟨_, haY⟩ ⟨_, hbY⟩
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val hcomm
  constructor
  · refine ⟨⟨fun a b => ?_⟩⟩
    have hxP : (((⟨(a : G), hPK a.2⟩ : ↥K) *
        ⟨(b : G), hPK b.2⟩ : ↥K) : G) ∈ P := by
      rw [Subgroup.coe_mul]
      exact P.mul_mem a.2 b.2
    have hyP : (((⟨(b : G), hPK b.2⟩ : ↥K) *
        ⟨(a : G), hPK a.2⟩ : ↥K) : G) ∈ P := by
      rw [Subgroup.coe_mul]
      exact P.mul_mem b.2 a.2
    have hxy : φ ((⟨(a : G), hPK a.2⟩ : ↥K) * ⟨(b : G), hPK b.2⟩) =
        φ ((⟨(b : G), hPK b.2⟩ : ↥K) * ⟨(a : G), hPK a.2⟩) := by
      rw [map_mul, map_mul]
      exact key a b
    have h := congrArg Subtype.val (SevenNineCompl.injective hφ hP hxP hyP hxy)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    simpa [Subgroup.coe_mul] using h
  · intro x hx
    have hxY : φ (⟨x, hPK hx⟩ : ↥K) ∈ Yb := by
      rw [← hbar]
      exact mem_barSub.mpr ⟨⟨x, hPK hx⟩, hx, rfl⟩
    have hpow : (φ (⟨x, hPK hx⟩ : ↥K)) ^ p = 1 := hc.elemAbelian.2 _ hxY
    have hxP : (((⟨x, hPK hx⟩ : ↥K)) ^ p : G) ∈ P := by
      simpa using P.pow_mem hx p
    have hφpow : φ ((⟨x, hPK hx⟩ : ↥K) ^ p) = φ (1 : ↥K) := by
      rw [map_pow, hpow, map_one]
    have heq : (⟨x, hPK hx⟩ : ↥K) ^ p = 1 :=
      SevenNineCompl.injective hφ hP hxP P.one_mem hφpow
    have hval := congrArg Subtype.val heq
    rw [Subgroup.coe_pow] at hval
    simpa using hval

theorem SevenNineCompl.barSub_inf_centralizer (h : Hyp73 V H E J) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) J φ) {L : Subgroup X} {p : ℕ}
    {Yb Zb : Subgroup X} (hc : SevenNineConfig L (barSub (kSub V H E) φ V) p Yb Zb) {v : G}
    (hvV : v ∈ V) (hvJ : v ∉ J) {P : Subgroup G} (hP : SevenNineCompl (kSub V H E) J φ Yb v P) :
    barSub (kSub V H E) φ (P ⊓ Subgroup.centralizer ({v} : Set G)) = Zb := by
  let K := kSub V H E
  let Vb := barSub K φ V
  let v' : ↥K := ⟨v, le_kSub h.mem hvV⟩
  change barSub K φ (P ⊓ Subgroup.centralizer ({v} : Set G)) = Zb
  have hbar : barSub K φ P = Yb := SevenNineCompl.barSub_eq hφ hP
  have hz : Zb = Yb ⊓ Subgroup.centralizer (Vb : Set X) := hc.z_eq
  have hVb : Vb = Subgroup.zpowers (φ v') :=
    SevenNineConfig.barSub_eq_zpowers h hφ hc hvV hvJ
  apply le_antisymm
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_barSub.mp hx
    obtain ⟨hkP, hkC⟩ := Subgroup.mem_inf.mp hk
    have hY : φ k ∈ Yb := by
      rw [← hbar]
      exact mem_barSub.mpr ⟨k, hkP, rfl⟩
    have hkv : v * (k : G) = (k : G) * v :=
      (Subgroup.mem_centralizer_iff.mp hkC) v (Set.mem_singleton v)
    have hcomm : φ v' * φ k = φ k * φ v' := by
      have hkv' : v' * k = k * v' := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact hkv
      calc φ v' * φ k = φ (v' * k) := by rw [map_mul]
        _ = φ (k * v') := by rw [hkv']
        _ = φ k * φ v' := by rw [map_mul]
    have hz' : φ k ∈ Subgroup.centralizer (Subgroup.zpowers (φ v') : Set X) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hcomm
    rw [hz, hVb]
    exact ⟨hY, hz'⟩
  · intro y hy
    have hyY : y ∈ Yb := by
      have h := hy
      rw [hz] at h
      exact (Subgroup.mem_inf.mp h).1
    have hyC : y ∈ Subgroup.centralizer (Vb : Set X) := by
      have h := hy
      rw [hz] at h
      exact (Subgroup.mem_inf.mp h).2
    have hyP : y ∈ barSub K φ P := by rw [hbar]; exact hyY
    obtain ⟨k, hkP, hkφ⟩ := mem_barSub.mp hyP
    have hcomm_y : φ v' * y = y * φ v' := by
      rw [hVb] at hyC
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_iff] at hyC
      exact hyC (φ v') (Set.mem_singleton (φ v'))
    have htk : φ v' * φ k = φ k * φ v' := by rw [hkφ]; exact hcomm_y
    have hconj_phi : φ (v' * k * v'⁻¹) = φ k := by
      rw [map_mul, map_mul, map_inv, htk]
      group
    have hwP : ((v' * k * v'⁻¹ : ↥K) : G) ∈ P := by
      have hn := (Subgroup.mem_normalizer_iff.mp hP.mem_normalizer) ((k : G))
      have hmem : v * (k : G) * v⁻¹ ∈ P := hn.mp hkP
      rw [show ((v' * k * v'⁻¹ : ↥K) : G) = v * (k : G) * v⁻¹ from by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]]
      exact hmem
    have heq : v' * k * v'⁻¹ = k := SevenNineCompl.injective hφ hP hwP hkP hconj_phi
    refine mem_barSub.mpr ⟨k, ?_, hkφ⟩
    refine ⟨hkP, ?_⟩
    refine (Subgroup.mem_centralizer_iff).mpr ?_
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have hcoe : v * (k : G) * v⁻¹ = (k : G) := by
      have hval := congrArg Subtype.val heq
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at hval
      exact hval
    calc v * (k : G) = v * (k : G) * v⁻¹ * v := by group
      _ = (k : G) * v := by rw [hcoe]

theorem SevenNineCompl.card_inf_centralizer (h : Hyp73 V H E J) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) J φ) {L : Subgroup X} {p : ℕ}
    {Yb Zb : Subgroup X} (hc : SevenNineConfig L (barSub (kSub V H E) φ V) p Yb Zb) {v : G}
    (hvV : v ∈ V) (hvJ : v ∉ J) {P : Subgroup G} (hP : SevenNineCompl (kSub V H E) J φ Yb v P) :
    Nat.card ↥(P ⊓ Subgroup.centralizer ({v} : Set G)) * p = Nat.card P := by
  let K := kSub V H E
  let Cv := P ⊓ Subgroup.centralizer ({v} : Set G)
  change Nat.card ↥Cv * p = Nat.card P
  have hCv : Cv ≤ P := inf_le_left
  have hcardCv : Nat.card (barSub K φ Cv) = Nat.card Cv :=
    SevenNineCompl.card_barSub_of_le hφ hP hCv
  have hcardP : Nat.card (barSub K φ P) = Nat.card P :=
    SevenNineCompl.card_barSub_of_le hφ hP le_rfl
  have hbarCv : barSub K φ Cv = Zb := SevenNineCompl.barSub_inf_centralizer h hφ hc hvV hvJ hP
  have hbarP : barSub K φ P = Yb := SevenNineCompl.barSub_eq hφ hP
  rw [← hcardCv, hbarCv, ← hcardP, hbarP]
  exact hc.card_z

theorem SevenNineCompl.barSub_commutator (h : Hyp73 V H E J) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) J φ) {L : Subgroup X} {p : ℕ}
    {Yb Zb : Subgroup X} (hc : SevenNineConfig L (barSub (kSub V H E) φ V) p Yb Zb) {v : G}
    (hvV : v ∈ V) (hvJ : v ∉ J) {P : Subgroup G} (hP : SevenNineCompl (kSub V H E) J φ Yb v P) :
    barSub (kSub V H E) φ ⁅P, Subgroup.zpowers v⁆ = ⁅Yb, barSub (kSub V H E) φ V⁆ := by
  let K := kSub V H E
  let v' : ↥K := ⟨v, le_kSub h.mem hvV⟩
  change barSub K φ ⁅P, Subgroup.zpowers v⁆ = ⁅Yb, barSub K φ V⁆
  have hPK : P ≤ K := hP.le.trans (barPre_le K φ Yb)
  have hvK : Subgroup.zpowers v ≤ K := Subgroup.zpowers_le.mpr (le_kSub h.mem hvV)
  have hcommK : ⁅P, Subgroup.zpowers v⁆ ≤ K :=
    (Subgroup.commutator_le_sup P (Subgroup.zpowers v)).trans (sup_le hPK hvK)
  have hsub : (⁅P, Subgroup.zpowers v⁆).subgroupOf K =
      ⁅P.subgroupOf K, (Subgroup.zpowers v).subgroupOf K⁆ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_commutator,
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hcommK, inf_eq_left.mpr hPK, inf_eq_left.mpr hvK]
  have hzv : (Subgroup.zpowers v).subgroupOf K = Subgroup.zpowers v' := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hn)⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by
        have h := congrArg Subtype.val hn
        rw [Subgroup.coe_zpow] at h
        exact h⟩
  have hvbar : barSub K φ (Subgroup.zpowers v) = Subgroup.zpowers (φ v') := by
    change ((Subgroup.zpowers v).subgroupOf K).map φ = Subgroup.zpowers (φ v')
    rw [hzv, MonoidHom.map_zpowers]
  have hPbar : barSub K φ P = Yb := SevenNineCompl.barSub_eq hφ hP
  have hVb : barSub K φ V = Subgroup.zpowers (φ v') :=
    SevenNineConfig.barSub_eq_zpowers h hφ hc hvV hvJ
  calc barSub K φ ⁅P, Subgroup.zpowers v⁆
      = ((⁅P, Subgroup.zpowers v⁆).subgroupOf K).map φ := rfl
    _ = (⁅P.subgroupOf K, (Subgroup.zpowers v).subgroupOf K⁆).map φ := by rw [hsub]
    _ = ⁅(P.subgroupOf K).map φ, ((Subgroup.zpowers v).subgroupOf K).map φ⁆ :=
        Subgroup.map_commutator (P.subgroupOf K) ((Subgroup.zpowers v).subgroupOf K) φ
    _ = ⁅barSub K φ P, barSub K φ (Subgroup.zpowers v)⁆ := rfl
    _ = ⁅Yb, Subgroup.zpowers (φ v')⁆ := by rw [hPbar, hvbar]
    _ = ⁅Yb, barSub K φ V⁆ := by rw [hVb]

end CFSG.LocalAnalysis.WeakClosure81
