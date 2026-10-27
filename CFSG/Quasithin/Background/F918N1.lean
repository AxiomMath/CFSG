module

public import CFSG.Quasithin.Background.F918M5
public import CFSG.Quasithin.Background.F918P4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeSecHom
public import CFSG.Quasithin.Background.B1More8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Matrix commutatorElement

section General

private theorem n1_isQuotientOfSQTK_of_le {G : Type*} [Group G] {M N : Subgroup G} (hNM : N ≤ M)
    (hM : IsQuotientOfSQTKTC ↥M) : IsQuotientOfSQTKTC ↥N := by
  obtain ⟨S, _, _, hSQT, hK, φ, hφ⟩ := hM
  let N' : Subgroup ↥M := N.subgroupOf M
  refine ⟨↥(N'.comap φ), inferInstance, inferInstance, ?_, hK.subgroup _, ?_⟩
  · intro p hp hp2
    exact (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt (N'.comap φ).subtype
      (N'.comap φ).subtype_injective).trans (hSQT p hp hp2)
  · refine ⟨(Subgroup.subgroupOfEquivOfLe hNM).toMonoidHom.comp (φ.subgroupComap N'), ?_⟩
    exact (Subgroup.subgroupOfEquivOfLe hNM).surjective.comp
      (MonoidHom.subgroupComap_surjective φ N' hφ)

private theorem n1_isQuotientOfSQTK_range {N : Type*} [Group N] {Γ : Type*} [Group Γ] (ρ : N →* Γ)
    (hN : IsQuotientOfSQTKTC N) : IsQuotientOfSQTKTC ↥ρ.range := by
  obtain ⟨S, _, _, h1, h2, φ, hφ⟩ := hN
  exact ⟨S, inferInstance, inferInstance, h1, h2, ρ.rangeRestrict.comp φ,
    ρ.rangeRestrict_surjective.comp hφ⟩

private theorem n1_isQuasisimple_map {G Γ : Type*} [Group G] [Group Γ] {L X : Subgroup G}
    (hLX : L ≤ X) (hL : CFSG.IsQuasisimple ↥L) (φ : ↥X →* Γ)
    (hne : (L.subgroupOf X).map φ ≠ ⊥) : CFSG.IsQuasisimple ↥((L.subgroupOf X).map φ) := by
  let ψ : ↥L →* ↥((L.subgroupOf X).map φ) :=
    (φ.comp (Subgroup.inclusion hLX)).codRestrict _
      (fun l => ⟨⟨(l : G), hLX l.2⟩, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩)
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.2
    exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext hxy⟩
  obtain ⟨y, hy⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  obtain ⟨l, rfl⟩ := hsurj y
  exact CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hL hsurj ⟨l, hy⟩

private theorem n1_le_normalizer {G : Type*} [Group G] {H N : Subgroup G}
    (h : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N) : H ≤ Subgroup.normalizer (N : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨h g hg n, fun hn => ?_⟩
  have h1 := h g⁻¹ (H.inv_mem hg) _ hn
  have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
  rwa [e] at h1

private theorem n1_pow_card_mem {G : Type*} [Group G] {Mp T : Subgroup G} [Finite T]
    (hTn : T ≤ Subgroup.normalizer (Mp : Set G)) {g : G} (hg : g ∈ Mp ⊔ T) : g ^ Nat.card T ∈ Mp := by
  have hg' : g ∈ ((Mp ⊔ T : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Mp T hTn] at hg'
  obtain ⟨m, hm, t, ht, rfl⟩ := hg'
  have key : ∀ n : ℕ, (m * t) ^ n * (t ^ n)⁻¹ ∈ Mp := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have htn : t ^ n * m * (t ^ n)⁻¹ ∈ Mp :=
        (Subgroup.mem_normalizer_iff.mp (hTn (T.pow_mem ht n)) m).mp hm
      have e : (m * t) ^ (n + 1) * (t ^ (n + 1))⁻¹ =
          ((m * t) ^ n * (t ^ n)⁻¹) * (t ^ n * m * (t ^ n)⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      rw [e]
      exact Mp.mul_mem ih htn
  have ht1 : t ^ Nat.card T = 1 := by
    have h := pow_card_eq_one' (G := ↥T) (x := ⟨t, ht⟩)
    exact congrArg Subtype.val h
  have h := key (Nat.card T)
  rwa [ht1, inv_one, mul_one] at h

end General

section Maps

variable {W : Type} [CommGroup W]

private noncomputable def n1Sec {G : Subgroup (MulAut W)} {Y U : Subgroup W}
    (hG : G ≤ stabSub Y ⊓ stabSub U) : ↥G →* MulAut (Sec Y U) :=
  (Bridge.secHom Y U).comp (Subgroup.inclusion hG)

private noncomputable def n1Res {G : Subgroup (MulAut W)} {Y : Subgroup W} (hG : G ≤ stabSub Y) :
    ↥G →* MulAut ↥Y :=
  (resHom Y).comp (Subgroup.inclusion hG)

private theorem n1Sec_eq_one_iff {G : Subgroup (MulAut W)} {Y U : Subgroup W}
    (hG : G ≤ stabSub Y ⊓ stabSub U) (x : ↥G) : n1Sec hG x = 1 ↔ (x : MulAut W) ∈ centSec Y U :=
  Bridge.secHom_eq_one_iff (Subgroup.inclusion hG x)

private theorem n1Res_eq_one_iff {G : Subgroup (MulAut W)} {Y : Subgroup W} (hG : G ≤ stabSub Y)
    (x : ↥G) : n1Res hG x = 1 ↔ (x : MulAut W) ∈ centSub Y := by
  constructor
  · intro h u hu
    exact congrArg (fun φ : MulAut ↥Y => ((φ ⟨u, hu⟩ : ↥Y) : W)) h
  · intro h
    ext u
    exact h u u.2

private theorem n1_autSec_eq_map {G X : Subgroup (MulAut W)} {Y U : Subgroup W}
    (hG : G ≤ stabSub Y ⊓ stabSub U) (hXG : X ≤ G) : autSec X Y U = (X.subgroupOf G).map (n1Sec hG) := by
  ext ψ
  rw [Bridge.mem_autSec_iff_secHom (hXG.trans hG), Subgroup.mem_map]
  constructor
  · rintro ⟨g, hgX, rfl⟩
    exact ⟨⟨(g : MulAut W), hXG hgX⟩, Subgroup.mem_subgroupOf.mpr hgX, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨Subgroup.inclusion hG g, Subgroup.mem_subgroupOf.mp hg, rfl⟩

private theorem n1_autSub_eq_map {G X : Subgroup (MulAut W)} {Y : Subgroup W} (hG : G ≤ stabSub Y)
    (hXG : X ≤ G) : autSub X Y = (X.subgroupOf G).map (n1Res hG) := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    exact ⟨⟨(g : MulAut W), hXG hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact mem_autSub.mpr ⟨⟨(g : MulAut W), hG g.2⟩, Subgroup.mem_subgroupOf.mp hg, rfl⟩

private theorem n1_conj_mem_centSec {Y U : Subgroup W} {g k : MulAut W} (hgY : g ∈ stabSub Y)
    (hgU : g ∈ stabSub U) (hk : k ∈ centSec Y U) : g * k * g⁻¹ ∈ centSec Y U :=
  CFSG.Quasithin.StabLat.conj_mem_centSec hgY hgU hk

end Maps

section Setup

variable {W : Type} [CommGroup W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

private theorem n1_T_le_normalizer (hD : D31 M Mp T L V) :
    T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
  rw [hD.Mp_eq]; exact le_normalizer_conjClosure L T

private theorem n1_L_le_Mp (hD : D31 M Mp T L V) : L ≤ Mp := by
  rw [hD.Mp_eq]; exact le_conjClosure L T

private theorem n1_sup_le_M (hD : D31 M Mp T L V) : Mp ⊔ T ≤ M := by
  refine sup_le ?_ hD.sylow.1
  rw [hD.Mp_eq]
  exact conjClosure_le fun s hs l hl =>
    M.mul_mem (M.mul_mem (hD.sylow.1 hs) (le_of_mem_cComp hD.comp hl)) (M.inv_mem (hD.sylow.1 hs))

private theorem n1_Mp_le_stabSub_orbSup (hD : D31 M Mp T L V) : Mp ≤ stabSub (orbSup T V) := by
  have hTn := n1_T_le_normalizer hD
  have hinv : ∀ x ∈ Mp, ∀ v ∈ V, x v ∈ V := (mem_irrPlus_top_iff.mp hD.irr).1
  refine B1.le_stabSub_of_invariant fun x hx u hu => ?_
  have hle : orbSup T V ≤ (orbSup T V).comap x.toMonoidHom := by
    refine orbSup_le fun s hs => ?_
    rintro _ ⟨v, hv, rfl⟩
    have hx' : s⁻¹ * x * s ∈ Mp := (Subgroup.mem_normalizer_iff''.mp (hTn hs) x).mp hx
    show x (s v) ∈ orbSup T V
    have h1 : x (s v) = s ((s⁻¹ * x * s) v) := by simp [MulAut.mul_apply]
    rw [h1]
    exact map_le_orbSup hs ⟨_, hinv _ hx' v hv, rfl⟩
  exact hle hu

private theorem n1_sup_le_stabSub_fixV (hD : D31 M Mp T L V) : Mp ⊔ T ≤ stabSub (fixV Mp) := by
  have hTn := n1_T_le_normalizer hD
  refine sup_le (fun m hm => centSub_le_stabSub _ fun w hw => hw m hm) ?_
  refine B1.le_stabSub_of_invariant fun t ht w hw m hm => ?_
  have hm' : t⁻¹ * m * t ∈ Mp := (Subgroup.mem_normalizer_iff''.mp (hTn ht) m).mp hm
  have h1 : m (t w) = t ((t⁻¹ * m * t) w) := by simp [MulAut.mul_apply]
  rw [h1, hw _ hm']

theorem n1_sup_le_stabSub_sec (hD : D31 M Mp T L V) :
    Mp ⊔ T ≤ stabSub (orbSup T V) ⊓ stabSub (orbSup T V ⊓ fixV Mp) := by
  have h1 : Mp ⊔ T ≤ stabSub (orbSup T V) :=
    sup_le (n1_Mp_le_stabSub_orbSup hD) (le_stabSub_orbSup T V)
  have h2 := n1_sup_le_stabSub_fixV hD
  refine le_inf h1 fun g hg u => ?_
  rw [Subgroup.mem_inf, Subgroup.mem_inf, h1 hg u, h2 hg u]

theorem n1_autSec_sup (hD : D31 M Mp T L V) :
    autSec Mp (orbSup T V) (orbSup T V ⊓ fixV Mp) ⊔ autSec T (orbSup T V) (orbSup T V ⊓ fixV Mp) =
      autSec (Mp ⊔ T) (orbSup T V) (orbSup T V ⊓ fixV Mp) := by
  have hG := n1_sup_le_stabSub_sec hD
  rw [n1_autSec_eq_map hG le_sup_left, n1_autSec_eq_map hG le_sup_right, n1_autSec_eq_map hG le_rfl,
    ← Subgroup.map_sup,
    ← Subgroup.subgroupOf_sup (le_sup_left : Mp ≤ Mp ⊔ T) (le_sup_right : T ≤ Mp ⊔ T)]

private theorem n1_sq_apply (hD : D31 M Mp T L V) {k : MulAut W} (hkM : k ∈ Mp)
    (hk : k ∈ centSec (orbSup T V) (orbSup T V ⊓ fixV Mp)) : ∀ w ∈ orbSup T V, (k ^ 2) w = w := by
  intro w hw
  have hc := (mem_centSec.mp hk).2 w hw
  have hkc : k (k w * w⁻¹) = k w * w⁻¹ := hc.2 k hkM
  have e : k w = (k w * w⁻¹) * w := by rw [inv_mul_cancel_right]
  have hsq : (k w * w⁻¹) * (k w * w⁻¹) = 1 := by rw [← pow_two]; exact hD.exp _
  calc (k ^ 2) w = k (k w) := by rw [pow_two, MulAut.mul_apply]
    _ = k ((k w * w⁻¹) * w) := by rw [← e]
    _ = (k w * w⁻¹) * k w := by rw [map_mul, hkc]
    _ = (k w * w⁻¹) * ((k w * w⁻¹) * w) := by rw [← e]
    _ = w := by rw [← mul_assoc, hsq, one_mul]

end Setup

section Kernel

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

theorem n1_inf_centSec_le_centSub (hD : D3Std M Mp T L V) :
    (Mp ⊔ T) ⊓ centSec (orbSup T V) (orbSup T V ⊓ fixV Mp) ≤ centSub (orbSup T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG := n1_sup_le_stabSub_sec hD.hyp
  have hGs : Mp ⊔ T ≤ stabSub (orbSup T V) := hG.trans inf_le_left
  set K : Subgroup (MulAut W) := (Mp ⊔ T) ⊓ centSec (orbSup T V) (orbSup T V ⊓ fixV Mp) with hK
  have hKs : K ≤ stabSub (orbSup T V) := inf_le_left.trans hGs
  have hPG : autSub K (orbSup T V) ≤ autSub (Mp ⊔ T) (orbSup T V) := autSub_mono inf_le_left _
  have hPn : autSub (Mp ⊔ T) (orbSup T V) ≤
      Subgroup.normalizer (autSub K (orbSup T V) : Set (MulAut ↥(orbSup T V))) := by
    refine n1_le_normalizer fun φ hφ ψ hψ => ?_
    obtain ⟨g, hgG, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨k, hkK, rfl⟩ := mem_autSub.mp hψ
    have hgk : (g : MulAut W) * k * (g : MulAut W)⁻¹ ∈ K :=
      ⟨(Mp ⊔ T).mul_mem ((Mp ⊔ T).mul_mem hgG hkK.1) ((Mp ⊔ T).inv_mem hgG),
        n1_conj_mem_centSec (hG hgG).1 (hG hgG).2 hkK.2⟩
    refine mem_autSub.mpr ⟨g * k * g⁻¹, hgk, ?_⟩
    rw [map_mul, map_mul, map_inv]
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hD.hyp.sylow.2.1
  have hP2 : IsPGroup 2 (autSub K (orbSup T V)) := by
    rintro ⟨φ, hφ⟩
    obtain ⟨k, hkK, rfl⟩ := mem_autSub.mp hφ
    refine ⟨e + 1, Subtype.ext ?_⟩
    have hk1 : (k : MulAut W) ^ Nat.card T ∈ Mp := n1_pow_card_mem (n1_T_le_normalizer hD.hyp) hkK.1
    have hk2 : (k : MulAut W) ^ Nat.card T ∈ centSec (orbSup T V) (orbSup T V ⊓ fixV Mp) :=
      Subgroup.pow_mem _ hkK.2 _
    have hsq := n1_sq_apply hD.hyp hk1 hk2
    rw [Subgroup.coe_pow, ← map_pow]
    ext u
    show ((k : MulAut W) ^ 2 ^ (e + 1)) (u : W) = u
    rw [pow_succ, pow_mul, ← he]
    exact hsq u u.2
  have hPO : autSub K (orbSup T V) ≤ pCoreOf 2 (autSub (Mp ⊔ T) (orbSup T V)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPG hPn hP2
  rw [D31.pCoreOf_autSub_orbSup_eq_bot hD.hyp] at hPO
  intro k hk w hw
  have hmem : resHom (orbSup T V) ⟨k, hKs hk⟩ ∈ autSub K (orbSup T V) :=
    mem_autSub.mpr ⟨⟨k, hKs hk⟩, hk, rfl⟩
  have h1 := hPO hmem
  rw [Subgroup.mem_bot] at h1
  exact congrArg (fun φ : MulAut ↥(orbSup T V) => ((φ ⟨w, hw⟩ : ↥(orbSup T V)) : W)) h1

theorem n1_autSub_inf_centQuot_eq_bot (hD : D3Std M Mp T L V) :
    autSub (Mp ⊔ T) (orbSup T V) ⊓ centQuot ((orbSup T V ⊓ fixV Mp).subgroupOf (orbSup T V)) = ⊥ := by
  rw [eq_bot_iff]
  rintro φ ⟨hφ, hφc⟩
  obtain ⟨g, hgG, rfl⟩ := mem_autSub.mp hφ
  rw [Subgroup.mem_bot]
  have hcs : (g : MulAut W) ∈ centSec (orbSup T V) (orbSup T V ⊓ fixV Mp) := by
    refine mem_centSec.mpr ⟨g.2, fun w hw => ?_⟩
    have h1 := (mem_centQuot.mp hφc) ⟨w, hw⟩
    rw [Subgroup.mem_subgroupOf] at h1
    exact h1
  have h2 := n1_inf_centSec_le_centSub hD ⟨hgG, hcs⟩
  ext u
  exact h2 u u.2

end Kernel

section QuotParams

variable {Y : Type} [CommGroup Y] {U : Subgroup Y}

private theorem n1_commIter_autQuot_le (A : Subgroup (MulAut Y)) (n : ℕ) :
    commIter ⊤ (autQuot A U) n ≤ (commIter ⊤ A n).map (QuotientGroup.mk' U) := by
  induction n with
  | zero =>
    show (⊤ : Subgroup (Y ⧸ U)) ≤ (⊤ : Subgroup Y).map (QuotientGroup.mk' U)
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective U)]
  | succ n ih =>
    show commSub (commIter ⊤ (autQuot A U) n) (autQuot A U) ≤
      (commSub (commIter ⊤ A n) A).map (QuotientGroup.mk' U)
    refine (commSub_mono ih le_rfl).trans ?_
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨φ, hφ, _, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨g, hgA, rfl⟩ := mem_autQuot.mp hφ
    refine ⟨(g : MulAut Y) y * y⁻¹, Subgroup.subset_closure ⟨g, hgA, y, hy, rfl⟩, ?_⟩
    rw [map_mul, map_inv]
    rfl

private theorem n1_commSeries_autQuot_eq_bot {A : Subgroup (MulAut Y)} {k : ℕ}
    (h : commSeries A k = ⊥) : commSeries (autQuot A U) k = ⊥ := by
  have h1 := n1_commIter_autQuot_le (U := U) A k
  rw [show commIter ⊤ A k = commSeries A k from rfl, h, Subgroup.map_bot] at h1
  exact le_bot_iff.mp h1

variable [Finite Y]

theorem n1_rkIdx_fixV_autQuot_le (hY : ∀ y : Y, y ^ 2 = 1) (A : Subgroup (MulAut Y)) :
    rkIdx (fixV (autQuot A U)) ≤ rkIdx (fixV A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY2 : IsPGroup 2 Y := fun v => ⟨1, by simpa using hY v⟩
  have hS2 : IsPGroup 2 (Y ⧸ U) := fun s => ⟨1, by simpa using sq_eq_one_quotient hY U s⟩
  obtain ⟨m, hm⟩ := hY2.index (fixV A)
  obtain ⟨m', hm'⟩ := hS2.index (fixV (autQuot A U))
  have h1 := Subgroup.index_mul_card (fixV A)
  have h2 := Subgroup.index_mul_card (fixV (autQuot A U))
  have h3 : Nat.card ↥(fixV A) ≤ Nat.card ↥(fixV (autQuot A U)) * Nat.card ↥U :=
    (card_fixV_le_autQuot (A := A) (U := U)).trans
      (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le inf_le_left))
  have h4 : Nat.card (Y ⧸ U) * Nat.card ↥U = Nat.card Y :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup U).symm
  have hle : 2 ^ m' ≤ 2 ^ m := by
    have hpos : 0 < Nat.card ↥(fixV (autQuot A U)) * Nat.card ↥U :=
      Nat.mul_pos Nat.card_pos Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc 2 ^ m' * (Nat.card ↥(fixV (autQuot A U)) * Nat.card ↥U)
        = Nat.card (Y ⧸ U) * Nat.card ↥U := by rw [← hm', ← mul_assoc, h2]
      _ = Nat.card Y := h4
      _ = 2 ^ m * Nat.card ↥(fixV A) := by rw [← hm, h1]
      _ ≤ 2 ^ m * (Nat.card ↥(fixV (autQuot A U)) * Nat.card ↥U) := Nat.mul_le_mul_left _ h3
  unfold rkIdx
  rw [hm, hm', padicValNat.prime_pow, padicValNat.prime_pow]
  exact (Nat.pow_le_pow_iff_right one_lt_two).mp hle

theorem n1_kq_autQuot_le (hY : ∀ y : Y, y ^ 2 = 1) {X : Subgroup (MulAut Y)}
    (hX : X ≤ stabSub U) (hf : X ⊓ centQuot U = ⊥) (k : ℕ) : kq (autQuot X U) k ≤ kq X k := by
  by_cases htop : kq X k = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp htop
  rw [← hr]
  obtain ⟨A, hA, hAk, hAr⟩ := kq_le_iff.mp (le_of_eq hr.symm)
  have hAs : A ≤ stabSub U := hA.1.trans hX
  have hAf : A ⊓ centQuot U = ⊥ := le_bot_iff.mp (hf ▸ inf_le_inf_right _ hA.1)
  have hcard : Nat.card ↥(autQuot A U) = Nat.card ↥A := by
    have h := card_autQuot_mul hAs
    rw [hAf, Subgroup.card_bot, mul_one] at h
    exact h
  have hne : autQuot A U ≠ ⊥ := by
    intro hbot
    apply hA.2.1
    rw [← Subgroup.card_eq_one, ← hcard, hbot, Subgroup.card_bot]
  refine kq_le_iff.mpr ⟨autQuot A U, ⟨autQuot_mono hA.1 U, hne, isElemAbelian2_autQuot U hA.2.2⟩,
    n1_commSeries_autQuot_eq_bot hAk, le_trans ?_ hAr⟩
  unfold rAV
  have hrk : rk ↥(autQuot A U) = rk ↥A := by
    unfold rk
    rw [hcard]
  rw [hrk]
  have hpos : (0 : ℚ) < rk ↥A := by exact_mod_cast hA.rk_pos
  exact div_le_div_of_nonneg_right (by exact_mod_cast n1_rkIdx_fixV_autQuot_le hY A) hpos.le

end QuotParams

section Fields

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

theorem z35g_exp (hD : D3Std M Mp T L V) :
    ∀ x : Sec (orbSup T V) (orbSup T V ⊓ fixV Mp), x ^ 2 = 1 :=
  sq_eq_one_sec hD.hyp.exp _ _

theorem z35g_qsqtk (hD : D3Std M Mp T L V) :
    IsQuotientOfSQTKTC ↥(autSec Mp (orbSup T V) (orbSup T V ⊓ fixV Mp) ⊔
      autSec T (orbSup T V) (orbSup T V ⊓ fixV Mp)) := by
  have hG := n1_sup_le_stabSub_sec hD.hyp
  rw [n1_autSec_sup hD.hyp, n1_autSec_eq_map hG le_rfl, map_subgroupOf_self_eq_range]
  exact n1_isQuotientOfSQTK_range _ (n1_isQuotientOfSQTK_of_le (n1_sup_le_M hD.hyp) hD.hyp.qsqtk)

theorem z35g_sylow (hD : D3Std M Mp T L V) :
    IsSylowTwoOf (autSec T (orbSup T V) (orbSup T V ⊓ fixV Mp))
      (autSec Mp (orbSup T V) (orbSup T V ⊓ fixV Mp) ⊔ autSec T (orbSup T V) (orbSup T V ⊓ fixV Mp)) := by
  have hG := n1_sup_le_stabSub_sec hD.hyp
  rw [n1_autSec_sup hD.hyp, n1_autSec_eq_map hG le_rfl, n1_autSec_eq_map hG le_sup_right]
  exact isSylowTwoOf_map_subgroupOf _
    (F7.isSylowTwoOf_mono_right hD.hyp.sylow le_sup_right (n1_sup_le_M hD.hyp))

theorem z35g_quasi (hD : D3Std M Mp T L V) (hlt : V < orbSup T V)
    (hC : ∀ g ∈ Mp, (∀ v ∈ V, g v = v) → ∀ x ∈ Mp, g * x = x * g) :
    CFSG.IsQuasisimple ↥(autSec L (orbSup T V) (orbSup T V ⊓ fixV Mp)) := by
  have _ := hlt
  have hG := n1_sup_le_stabSub_sec hD.hyp
  have hLMp := n1_L_le_Mp hD.hyp
  have hLG : L ≤ Mp ⊔ T := hLMp.trans le_sup_left
  rw [n1_autSec_eq_map hG hLG]
  refine n1_isQuasisimple_map hLG hD.hyp.quasi _ ?_
  rw [← n1_autSec_eq_map hG hLG]
  intro hbot
  have htriv : ∀ l ∈ L, ∀ v ∈ V, l v = v := by
    intro l hl v hv
    have h1 : n1Sec hG ⟨l, hLG hl⟩ ∈ autSec L (orbSup T V) (orbSup T V ⊓ fixV Mp) := by
      rw [n1_autSec_eq_map hG hLG]
      exact ⟨⟨l, hLG hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    rw [hbot, Subgroup.mem_bot, n1Sec_eq_one_iff] at h1
    exact n1_inf_centSec_le_centSub hD ⟨hLG hl, h1⟩ v (le_orbSup T V hv)
  have hcomm : ⁅L, L⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hC a (hLMp ha) (htriv a ha) b (hLMp hb)).symm
  rw [perfect_of_mem_cComp hD.hyp.comp] at hcomm
  exact ne_bot_of_mem_cComp hD.hyp.comp hcomm

theorem z35g_Mp_eq (hD : D3Std M Mp T L V) :
    autSec Mp (orbSup T V) (orbSup T V ⊓ fixV Mp) =
      conjClosure (autSec L (orbSup T V) (orbSup T V ⊓ fixV Mp))
        (autSec T (orbSup T V) (orbSup T V ⊓ fixV Mp)) := by
  have hG := n1_sup_le_stabSub_sec hD.hyp
  have hLG : L ≤ Mp ⊔ T := (n1_L_le_Mp hD.hyp).trans le_sup_left
  have h := map_subgroupOf_conjClosure (n1Sec hG) hLG (le_sup_right : T ≤ Mp ⊔ T)
  rw [← hD.hyp.Mp_eq] at h
  rw [n1_autSec_eq_map hG le_sup_left, h, ← n1_autSec_eq_map hG hLG, ← n1_autSec_eq_map hG le_sup_right]

theorem z35g_comm_conj (hD : D3Std M Mp T L V) :
    ∀ s ∈ autSec T (orbSup T V) (orbSup T V ⊓ fixV Mp),
      conjAutSub s (autSec L (orbSup T V) (orbSup T V ⊓ fixV Mp)) =
          autSec L (orbSup T V) (orbSup T V ⊓ fixV Mp) ∨
        ⁅autSec L (orbSup T V) (orbSup T V ⊓ fixV Mp),
          conjAutSub s (autSec L (orbSup T V) (orbSup T V ⊓ fixV Mp))⁆ = ⊥ := by
  intro s hs
  have hG := n1_sup_le_stabSub_sec hD.hyp
  have hLG : L ≤ Mp ⊔ T := (n1_L_le_Mp hD.hyp).trans le_sup_left
  rw [n1_autSec_eq_map hG le_sup_right] at hs
  obtain ⟨t, -, rfl⟩ := hs
  rw [n1_autSec_eq_map hG hLG]
  have hLc : L ∈ cComp (Mp ⊔ T) := cComp_mem_of_le hD.hyp.comp hLG (n1_sup_le_M hD.hyp)
  have hK : CFSG.IsComponent (L.subgroupOf (Mp ⊔ T)) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLG).symm hD.hyp.quasi,
      A3.subnormal_top_iff.mp (subnormal_of_mem_cComp (subgroupOf_mem_cComp hLc))⟩
  have hKt := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hK
  have hconj : conjAutSub (n1Sec hG t) ((L.subgroupOf (Mp ⊔ T)).map (n1Sec hG)) =
      ((L.subgroupOf (Mp ⊔ T)).map (MulAut.conj t).toMonoidHom).map (n1Sec hG) := by
    unfold conjAutSub
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv]
  rw [hconj]
  rcases CFSG.LocalCores.distinct_components_commute hKt hK with h | h
  · left
    rw [h]
  · right
    rw [← Subgroup.map_commutator, Subgroup.commutator_comm, h, Subgroup.map_bot]

theorem z35g_o2 (hD : D3Std M Mp T L V) :
    pCoreOf 2 (autSec Mp (orbSup T V) (orbSup T V ⊓ fixV Mp) ⊔
      autSec T (orbSup T V) (orbSup T V ⊓ fixV Mp)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG := n1_sup_le_stabSub_sec hD.hyp
  have hGs : Mp ⊔ T ≤ stabSub (orbSup T V) := hG.trans inf_le_left
  have hker : ∀ x : ↥(Mp ⊔ T), n1Sec hG x = 1 → n1Res hGs x = 1 := fun x hx =>
    (n1Res_eq_one_iff hGs x).mpr
      (n1_inf_centSec_le_centSub hD ⟨x.2, (n1Sec_eq_one_iff hG x).mp hx⟩)
  rw [n1_autSec_sup hD.hyp, n1_autSec_eq_map hG le_rfl, map_subgroupOf_self_eq_range]
  have hYle : pCoreOf 2 (n1Sec hG).range ≤ (n1Sec hG).range := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hYn : (n1Sec hG).range ≤
      Subgroup.normalizer (pCoreOf 2 (n1Sec hG).range : Set (MulAut (Sec (orbSup T V) (orbSup T V ⊓ fixV Mp)))) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hY2 : IsPGroup 2 (pCoreOf 2 (n1Sec hG).range) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  set Yt : Subgroup ↥(Mp ⊔ T) := (pCoreOf 2 (n1Sec hG).range).comap (n1Sec hG) with hYt
  have hYtn : Yt.Normal := by
    refine ⟨fun y hy g => ?_⟩
    rw [hYt, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hYn ⟨g, rfl⟩) _).mp hy
  have hPle : Yt.map (n1Res hGs) ≤ autSub (Mp ⊔ T) (orbSup T V) := by
    rw [n1_autSub_eq_map hGs le_rfl, map_subgroupOf_self_eq_range]
    exact Subgroup.map_le_range _ _
  have hPn : autSub (Mp ⊔ T) (orbSup T V) ≤
      Subgroup.normalizer (Yt.map (n1Res hGs) : Set (MulAut ↥(orbSup T V))) := by
    rw [n1_autSub_eq_map hGs le_rfl, map_subgroupOf_self_eq_range]
    refine n1_le_normalizer ?_
    rintro _ ⟨g, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨g * y * g⁻¹, hYtn.conj_mem y hy g, by rw [map_mul, map_mul, map_inv]⟩
  have hP2 : IsPGroup 2 (Yt.map (n1Res hGs)) := by
    rintro ⟨_, y, hy, rfl⟩
    obtain ⟨n, hn⟩ := hY2 ⟨n1Sec hG y, hy⟩
    refine ⟨n, Subtype.ext ?_⟩
    have h1 : n1Sec hG (y ^ 2 ^ n) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hn
    have h2 := hker _ h1
    rw [map_pow] at h2
    exact h2
  have hPO : Yt.map (n1Res hGs) ≤ pCoreOf 2 (autSub (Mp ⊔ T) (orbSup T V)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPle hPn hP2
  rw [D31.pCoreOf_autSub_orbSup_eq_bot hD.hyp] at hPO
  rw [eq_bot_iff]
  intro φ hφ
  obtain ⟨x, rfl⟩ := hYle hφ
  have hx : x ∈ Yt := hφ
  have hσx : n1Res hGs x = 1 := Subgroup.mem_bot.mp (hPO ⟨x, hx, rfl⟩)
  rw [Subgroup.mem_bot, n1Sec_eq_one_iff]
  exact centSub_le_centSec _ _ ((n1Res_eq_one_iff hGs x).mp hσx)

theorem z35g_qhat (hD : D3Std M Mp T L V) :
    qhatOf (autSec Mp (orbSup T V) (orbSup T V ⊓ fixV Mp) ⊔
      autSec T (orbSup T V) (orbSup T V ⊓ fixV Mp)) ≤ ((2 : ℚ) : WithTop ℚ) := by
  have hG := n1_sup_le_stabSub_sec hD.hyp
  rw [n1_autSec_sup hD.hyp]
  have hX : autSub (Mp ⊔ T) (orbSup T V) ≤ stabSub ((orbSup T V ⊓ fixV Mp).subgroupOf (orbSup T V)) :=
    autSub_le_stabSub_subgroupOf (hG.trans inf_le_right)
  have hexp : ∀ u : ↥(orbSup T V), u ^ 2 = 1 := B1.sq_eq_one_sub hD.hyp.exp _
  exact (n1_kq_autQuot_le hexp hX (n1_autSub_inf_centQuot_eq_bot hD) 3).trans hD.qhat

end Fields

end CFSG.Quasithin
