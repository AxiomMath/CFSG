module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Irr
public import CFSG.Quasithin.Vol2.KGFact12618d
public import CFSG.Quasithin.Background.SmithC27OTwoZ
public import CFSG.Milestones.ASVolI.C137.A6Out
public import CFSG.Quasithin.EmptyFaithful.SBd5Perf
public import CFSG.Quasithin.H13.GoldschmidtC137H6Str

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
  CFSG.LieType.BorelTits
open CFSG.Quasithin.C124 CFSG.Quasithin.H13.U3.GC137

variable {G : Type} [Group G]

theorem burnsideC137_isHatA6 {L : Subgroup G}
    (h : IsHat (↥L ⧸ CFSG.pCore 2 ↥L) ↥(alternatingGroup (Fin 6))) : H13.A6.IsHatA6 L :=
  ⟨h.1.1, h.2.1, h.2.2⟩

theorem burnsideC137_le_blockU [Finite G] {X V L : Subgroup G} (hred : IsTwoReducedIn X V)
    (hLX : L ≤ X) (hn : X ≤ normalizer (L : Set G)) (hUU : ⁅⁅V, L⁆, L⁆ = ⁅V, L⁆) :
    ⁅V, L⁆ ≤ blockU L := by
  have hVX : V ≤ X := (le_pCoreOf_of_reduced hred).trans (pCoreOf_le 2 X)
  have hUL : ⁅V, L⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_right.mp (hVX.trans hn)
  have hXU : X ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := fun g hg =>
    SBd5.mem_normalizer_commutator_of (hred.2.1 hg) (hn hg)
  have hUV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp (hLX.trans hred.2.1)
  have hU2 : IsPGroup 2 ↥⁅V, L⁆ :=
    B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono hUV hred.2.2.1)
  have hUQ : ⁅V, L⁆ ≤ pCoreOf 2 L := le_pCoreOf_of_le_normalizer 2 hUL (hLX.trans hXU) hU2
  rw [← hUU]
  exact Subgroup.commutator_mono hUQ le_rfl

theorem burnsideC137_relIndex_pCoreOf (L : Subgroup G) :
    (pCoreOf 2 L).relIndex L = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hR : (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective L) _
  rw [Subgroup.relIndex, hR, Subgroup.index_eq_card]

theorem burnsideC137_card_autI_of_hatBlock [Finite G] {X V L : Subgroup G}
    (hred : IsTwoReducedIn X V) (hLX : L ≤ X) (hn : X ≤ normalizer (L : Set G))
    (hUU : ⁅⁅V, L⁆, L⁆ = ⁅V, L⁆) (hVL : ⁅V, L⁆ ≠ ⊥) (hU : IsElemAbelian 2 ⁅V, L⁆)
    (hB : IsHatA6Block L) :
    Nat.card ↥(autI hU L) = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hXU : X ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := fun g hg =>
    SBd5.mem_normalizer_commutator_of (hred.2.1 hg) (hn hg)
  have hLU : L ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := hLX.trans hXU
  have hle := burnsideC137_le_blockU hred hLX hn hUU
  have heq : ⁅V, L⁆ = blockU L :=
    (H13.Ch4.T4213N.eq_bot_or_eq_blockU_of_isHatA6Block hB hle hLU).resolve_left hVL
  have hcent : L ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) = pCoreOf 2 L := by
    rw [heq]
    exact hB.2.2.2
  have h1 : Nat.card ↥(autI hU L) = (L ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G)).relIndex L :=
    card_autOn_eq_relIndex hLU
  rw [h1, hcent, burnsideC137_relIndex_pCoreOf]

theorem burnsideC137_fixV_eq_bot {W : Type} [CommGroup W] (hsq : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup (MulAut W)} (hcomm : commV H = ⊤)
    (hirr : XMod.IsIrrSec ↥H (XMod.fixed ↥H (⊤ : Subgroup W)) (⊤ : Subgroup W)) {z : MulAut W} (hzH : z ∈ H)
    (hzc : ∀ h ∈ H, h * z = z * h) (h3 : z ^ 3 = 1) (hz1 : z ≠ 1) : fixV H = ⊥ := by
  have hz3 : ∀ w : W, z (z (z w)) = w := fun w => by
    have := congrArg (fun φ : MulAut W => φ w) h3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hzh : ∀ h ∈ H, ∀ w : W, h (z w) = z (h w) := fun h hh w => by
    have := congrArg (fun φ : MulAut W => φ w) (hzc h hh)
    simpa [MulAut.mul_apply] using this
  set C : Subgroup W :=
    { carrier := {w | z w = w}
      one_mem' := map_one z
      mul_mem' := fun {a b} ha hb => by
        change z (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        change z a⁻¹ = a⁻¹
        rw [map_inv, ha] } with hCdef
  have hmemC : ∀ w : W, w ∈ C ↔ z w = w := fun w => Iff.rfl
  have hfix : XMod.fixed ↥H (⊤ : Subgroup W) = fixV H := by
    ext w
    constructor
    · intro hw x hx
      exact hw.2 ⟨x, hx⟩
    · intro hw
      exact ⟨Subgroup.mem_top _, fun a => hw a a.2⟩
  have hCinv : XMod.IsInv ↥H C := by
    intro a c hc
    change z ((a : MulAut W) c) = (a : MulAut W) c
    rw [← hzh a a.2 c, (hmemC c).1 hc]
  have hfC : XMod.fixed ↥H (⊤ : Subgroup W) ≤ C := by
    intro w hw
    exact hw.2 ⟨z, hzH⟩
  have hCeq : C = fixV H := by
    rcases hirr.2 C hCinv hfC le_top with hC | hC
    · rw [hC, hfix]
    · exfalso
      apply hz1
      ext w
      have hw : w ∈ C := hC ▸ Subgroup.mem_top w
      rw [MulAut.one_apply]
      exact (hmemC w).1 hw
  let e : W →* W :=
    { toFun := fun w => w * z w * z (z w)
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul]
        ac_rfl }
  have he : ∀ w, e w = w * z w * z (z w) := fun _ => rfl
  have heC : ∀ w, e w ∈ fixV H := fun w => by
    rw [← hCeq, hmemC, he, map_mul, map_mul, hz3]
    rw [mul_comm (z w * z (z w)) w, mul_assoc]
  have hker : commV H ≤ e.ker := by
    show Subgroup.closure _ ≤ e.ker
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    have hxe : e (x v) = x (e v) := by
      rw [he, he, map_mul, map_mul, hzh x hx, hzh x hx, hzh x hx]
    rw [map_mul, map_inv, hxe, heC v x hx, mul_inv_cancel]
  rw [eq_bot_iff]
  intro c hc
  have hce : e c = 1 := hker (hcomm ▸ Subgroup.mem_top c)
  have hzc' : z c = c := hc z hzH
  rw [he, hzc', hzc', ← sq, hsq, one_mul] at hce
  exact (Subgroup.mem_bot).2 hce

theorem burnsideC137_o2Z_le_of_maximal [Finite G] {X T L M : Subgroup G}
    (hT : IsSylowTwoOf T X) (hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) (hL : L ∈ cComp X)
    (hperf : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L)) (hTM : T ≤ M) (hMX : M < X)
    (hmax : ∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X) : oTwoZIn L ≤ M := by
  by_contra hD
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hn : X ≤ normalizer (L : Set G) := le_normalizer_of_prod hT hprod hL
  have hDL : oTwoZIn L ≤ L := Subgroup.map_subtype_le _
  have hDX : oTwoZIn L ≤ X := hDL.trans hLX
  have hXD : X ≤ normalizer (oTwoZIn L : Set G) :=
    hn.trans (SmithC27.normalizer_le_normalizer_oTwoZIn L)
  have hsup : M ⊔ oTwoZIn L = X := by
    rcases hmax _ le_sup_left (sup_le hMX.le hDX) with h1 | h1
    · exact absurd (h1 ▸ (le_sup_right : oTwoZIn L ≤ M ⊔ oTwoZIn L)) hD
    · exact h1
  have hQT : pCoreOf 2 X ≤ T := pCoreOf_two_le_of_sylowIn hT.1 hT.2.1 hT.2.2
  have hOLX : pCoreOf 2 L ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLX)
      (hn.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)
  have hOLM : pCoreOf 2 L ≤ M := hOLX.trans (hQT.trans hTM)
  have hLM : L ≤ M := by
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
    set N : Subgroup ↥L := (M ⊓ L).subgroupOf L with hN
    have hNZ : N.map π ⊔ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊤ := by
      rw [eq_top_iff]
      intro q _
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      have hyX : (y : G) ∈ (↑(M ⊔ oTwoZIn L) : Set G) := by
        rw [hsup]
        exact hLX y.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right M _ (hMX.le.trans hXD)] at hyX
      obtain ⟨m, hm, d, hd, hmd⟩ := hyX
      have hdL : d ∈ L := hDL hd
      have hmL : m ∈ L := by
        have : m = (y : G) * d⁻¹ := by rw [← hmd]; group
        rw [this]
        exact L.mul_mem y.2 (L.inv_mem hdL)
      obtain ⟨hdL', hdc⟩ := mem_o2Z_gc.1 hd
      have hyy : y = (⟨m, hmL⟩ : ↥L) * ⟨d, hdL⟩ := Subtype.ext hmd.symm
      rw [hyy, QuotientGroup.mk_mul]
      exact Subgroup.mul_mem_sup ⟨⟨m, hmL⟩, Subgroup.mem_subgroupOf.2 ⟨hm, hmL⟩, rfl⟩ hdc
    have htop := eq_top_of_sup_le_center_gc hperf le_rfl hNZ
    intro l hl
    have hq : π ⟨l, hl⟩ ∈ N.map π := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨n, hn', hnπ⟩ := hq
    have hnl : (n : G) ∈ M := (Subgroup.mem_subgroupOf.1 hn').1
    have hk : n⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnπ
      exact hnπ
    have hk' : ((n⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ pCoreOf 2 L := ⟨_, hk, rfl⟩
    have hl' : l = (n : G) * ((n⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
    rw [hl']
    exact M.mul_mem hnl (hOLM hk')
  have hXM : X ≤ M := by
    intro x hx
    obtain ⟨l, hl, t, ht, rfl⟩ := hprod x hx
    exact M.mul_mem (hLM hl) (hTM ht)
  exact hMX.not_ge hXM

theorem burnsideC137_card_alt6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem burnsideC137_not_o2Z_le [Finite G] {X T L P M : Subgroup G} (hT : IsSylowTwoOf T X)
    (hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) (hL : L ∈ cComp X)
    (hH : IsHat (↥L ⧸ CFSG.pCore 2 ↥L) ↥(alternatingGroup (Fin 6)))
    (hTP : T ≤ P) (hPM : P ≤ M) (hMX : M < X) (h3 : P.relIndex M = 3)
    (hO : ¬ oTwoUpper P ≤ oTwoZIn L) : ¬ oTwoZIn L ≤ P := by
  intro hZP
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hn : X ≤ normalizer (L : Set G) := le_normalizer_of_prod hT hprod hL
  have hPX : P ≤ X := hPM.trans hMX.le
  have hTM : T ≤ M := hTP.trans hPM
  obtain ⟨e⟩ := hH.2.2
  set Q := ↥L ⧸ CFSG.pCore 2 ↥L with hQ
  set φ : Q →* ↥(alternatingGroup (Fin 6)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q)) with hφ
  set ψ : ↥L →* ↥(alternatingGroup (Fin 6)) := φ.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    with hψ
  have hψs : Function.Surjective ψ :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have hφk : ∀ q : Q, φ q = 1 ↔ q ∈ Subgroup.center Q := by
    intro q
    rw [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hψk : ∀ x : ↥L, ψ x = 1 ↔ (x : G) ∈ oTwoZIn L := by
    intro x
    rw [hψ, MonoidHom.comp_apply, hφk, QuotientGroup.mk'_apply]
    constructor
    · intro hx
      exact mem_o2Z_gc.2 ⟨x.2, hx⟩
    · intro hx
      obtain ⟨_, hc⟩ := mem_o2Z_gc.1 hx
      exact hc
  set PL := P.subgroupOf L with hPL
  set ML := M.subgroupOf L with hML
  have hkerP : ψ.ker ≤ PL := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hZP ((hψk x).1 (MonoidHom.mem_ker.1 hx)))
  have hkerM : ψ.ker ≤ ML := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hPM (hZP ((hψk x).1 (MonoidHom.mem_ker.1 hx))))
  have hPML : PL ≤ ML := fun x hx => Subgroup.mem_subgroupOf.2 (hPM (Subgroup.mem_subgroupOf.1 hx))
  have ha : (PL.map ψ).index = PL.index := Subgroup.index_map_eq PL hψs hkerP
  have hb : (ML.map ψ).index = ML.index := Subgroup.index_map_eq ML hψs hkerM
  have hSyl : IsSylowTwoOf (T ⊓ L) L := A4.isSylowTwoOf_inf_normal hT hLX hn
  have hodd : ¬ 2 ∣ PL.index := by
    intro h2
    have h1 : P.relIndex L ∣ T.relIndex L := Subgroup.relIndex_dvd_of_le_left L hTP
    have h2' : (T ⊓ L).relIndex L = T.relIndex L := Subgroup.inf_relIndex_right T L
    have h3 : 2 ∣ (T ⊓ L).relIndex L := by
      rw [h2']
      exact dvd_trans h2 h1
    exact hSyl.2.2 h3
  have hc : PL.relIndex ML * ML.index = PL.index := Subgroup.relIndex_mul_index hPML
  have hcle : PL.relIndex ML ≤ 3 := by
    have e1 : PL.relIndex ML = (P ⊓ L).relIndex (M ⊓ L) := by
      rw [← Subgroup.relIndex_subgroupOf (inf_le_right : M ⊓ L ≤ L), Subgroup.inf_subgroupOf_right,
        Subgroup.inf_subgroupOf_right]
    have e2 : (P ⊓ L).relIndex (M ⊓ L) = P.relIndex (M ⊓ L) := by
      have : P ⊓ L = P ⊓ (M ⊓ L) := by
        rw [← inf_assoc, inf_eq_left.2 hPM]
      rw [this, Subgroup.inf_relIndex_right]
    rw [e1, e2, ← h3]
    exact Subgroup.relIndex_le_of_le_right inf_le_left (by rw [h3]; norm_num)
  have hc1 : PL.relIndex ML ≠ 1 := by
    intro h1
    have hle : ML ≤ PL := Subgroup.relIndex_eq_one.1 h1
    have hMP : M ≤ P := by
      intro m hm
      obtain ⟨l, hl, t, ht, rfl⟩ := hprod m (hMX.le hm)
      have hlM : l ∈ M := by
        have : l = l * t * t⁻¹ := by group
        rw [this]
        exact M.mul_mem hm (M.inv_mem (hTM ht))
      have hlP : l ∈ P := Subgroup.mem_subgroupOf.1 (hle (Subgroup.mem_subgroupOf.2 hlM :
        (⟨l, hl⟩ : ↥L) ∈ ML))
      exact P.mul_mem hlP (hTP ht)
    have : P.relIndex M = 1 := Subgroup.relIndex_eq_one.2 hMP
    omega
  have hc0 : PL.relIndex ML ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hc3 : PL.relIndex ML = 3 := by
    have h2 : PL.relIndex ML ≠ 2 := by
      intro h2
      apply hodd
      rw [← hc, h2]
      exact dvd_mul_right 2 _
    omega
  obtain ⟨x, hxP, hxo, hxZ⟩ : ∃ x ∈ P, Odd (orderOf x) ∧ x ∉ oTwoZIn L := by
    by_contra hne
    push Not at hne
    apply hO
    rw [oTwoUpper, Subgroup.closure_le]
    rintro y ⟨hyP, hyo⟩
    exact hne y hyP hyo
  have hxL : x ∈ L := by
    have hTp : IsPGroup 2 T := hT.2.1
    refine B1Red.mem_of_odd_orderOf_of_mem_sup hTp (hT.1.trans hn) ?_ hxo
    obtain ⟨l, hl, t, ht, hlt⟩ := hprod x (hPX hxP)
    rw [hlt]
    exact Subgroup.mul_mem_sup hl ht
  set y : ↥(alternatingGroup (Fin 6)) := ψ ⟨x, hxL⟩ with hy
  have hy1 : y ≠ 1 := fun h => hxZ ((hψk ⟨x, hxL⟩).1 h)
  have hyP : y ∈ PL.map ψ := ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.2 hxP, rfl⟩
  have hyo : Odd (orderOf y) := by
    have h1 : orderOf y ∣ orderOf (⟨x, hxL⟩ : ↥L) := orderOf_map_dvd ψ _
    have h2 : orderOf (⟨x, hxL⟩ : ↥L) = orderOf x := Subgroup.orderOf_mk x hxL
    exact Odd.of_dvd_nat hxo (h2 ▸ h1)
  have hcardP : Nat.card ↥(PL.map ψ) * (PL.map ψ).index = 360 := by
    rw [Subgroup.card_mul_index, burnsideC137_card_alt6]
  have hb5 : (ML.map ψ).index ≤ 5 := by
    by_contra h6
    push Not at h6
    set a := (PL.map ψ).index with ha'
    have haodd : ¬ 2 ∣ a := by rw [ha]; exact hodd
    have ha3 : a = 3 * (ML.map ψ).index := by rw [ha, hb, ← hc, hc3]
    have hadvd : a ∣ 45 := by
      have h360 : a ∣ 8 * 45 := Dvd.intro_left _ hcardP
      have hcop2 : Nat.Coprime a 2 :=
        Nat.coprime_two_right.2 (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 haodd))
      have hcop : Nat.Coprime a 8 := Nat.Coprime.pow_right 3 hcop2
      exact Nat.Coprime.dvd_of_dvd_mul_left hcop h360
    have ha45 : a = 45 := by
      have hle : a ≤ 45 := Nat.le_of_dvd (by norm_num) hadvd
      obtain ⟨k, hk⟩ := hadvd
      interval_cases a <;> omega
    have hc8 : Nat.card ↥(PL.map ψ) = 8 := by
      rw [ha45] at hcardP
      omega
    have hdvd : orderOf y ∣ 2 ^ 3 := by
      have := Subgroup.orderOf_dvd_natCard (PL.map ψ) hyP
      rw [hc8] at this
      exact this
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hi0 : i = 0 := by
      rcases Nat.eq_zero_or_pos i with h | h
      · exact h
      · exfalso
        rw [hi'] at hyo
        exact (Nat.not_even_iff_odd.2 hyo) ((Nat.even_pow' h.ne').2 even_two)
    rw [hi0, pow_zero] at hi'
    exact hy1 (orderOf_eq_one_iff.1 hi')
  set M' : Subgroup Q := ML.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) with hM'
  have hmap : M'.map φ = ML.map ψ := by
    rw [hM', Subgroup.map_map]
  have hZc : ∀ z ∈ φ.ker, ∀ q : Q, z * q = q * z := by
    intro z hz q
    have hzc : z ∈ Subgroup.center Q := (hφk z).1 (MonoidHom.mem_ker.1 hz)
    exact (Subgroup.mem_center_iff.1 hzc q).symm
  have hperf : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤ := by
    rw [← _root_.commutator_def]
    exact Group.isPerfect_def.1 hH.1.1
  have htop : M' = ⊤ :=
    H13.KG12618.eq_top_of_map_index_le φ hZc hperf M' (by rw [hmap]; exact hb5)
  have hQT : pCoreOf 2 X ≤ T := pCoreOf_two_le_of_sylowIn hT.1 hT.2.1 hT.2.2
  have hOLX : pCoreOf 2 L ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLX)
      (hn.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)
  have hLM : L ≤ M := by
    intro l hl
    have hq : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨l, hl⟩ ∈ M' := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨m, hm, hmq⟩ := hq
    have hk : m⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hmq
      exact hmq
    have hk' : ((m⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ pCoreOf 2 L := ⟨_, hk, rfl⟩
    have hl' : l = (m : G) * ((m⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
    rw [hl']
    exact M.mul_mem (Subgroup.mem_subgroupOf.1 hm) (hOLX.trans (hQT.trans hTM) hk')
  apply hMX.not_ge
  intro x hx
  obtain ⟨l, hl, t, ht, rfl⟩ := hprod x hx
  exact M.mul_mem (hLM hl) (hTM ht)

open CFSG.Quasithin.B3 in
theorem burnsideC137_concl5_of_le [Finite G] {X T L P V U : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXV : X ≤ normalizer (V : Set G)) (hU : IsElemAbelian 2 U) (hUV : U ≤ V)
    (hXU : X ≤ normalizer (U : Set G)) (hXL : X ≤ normalizer (L : Set G)) (hLX : L ≤ X)
    (hTX : T ≤ X) (hC : X ⊓ centralizer (U : Set G) = X ⊓ centralizer (V : Set G))
    {k : Mod} (hk : k = Mod.ut0 ∨ k = Mod.u0) (N : KModel k (autI hU L))
    (hXeq : (⊤ : Subgroup (Gp 6)).map N.ρ = autI hU X)
    (hirr : XMod.IsIrrSec ↥(autI hU L) (XMod.fixed ↥(autI hU L) (⊤ : Subgroup (IntMod U hU)))
      (⊤ : Subgroup (IntMod U hU)))
    (hPl : ∀ l : Subgroup G, U ⊓ centralizer (L : Set G) ≤ l → l ≤ U →
      P ≤ normalizer (l : Set G) → ¬ X ≤ normalizer (l : Set G) →
      autOn P V = autOn (X ⊓ normalizer (l : Set G)) V)
    (hw : (∃ l : Subgroup G, U ⊓ centralizer (L : Set G) ≤ l ∧ l ≤ U ∧
        Nat.card ↥l = 4 * Nat.card ↥(U ⊓ centralizer (L : Set G)) ∧ P ≤ normalizer (l : Set G)) ∧
      (IsHat (↥L ⧸ CFSG.pCore 2 ↥L) ↥(alternatingGroup (Fin 6)) → ¬ oTwoUpper (oTwoZIn L) ≤ P) ∧
      ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ 2 < Nat.card ↥(autOn A U)) :
    burnsideC137_Concl5 X T L P V U := by
  have hLU : L ≤ normalizer (U : Set G) := hLX.trans hXU
  have hXZ : X ≤ normalizer ((U ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.1 (hXU hx) y
    have h2 := Subgroup.mem_normalizer_iff.1 (burnsideC137_mem_normalizer_centralizer (hXL hx)) y
    simp only [Subgroup.mem_inf]
    rw [h1, h2]
  obtain ⟨f, hfs, hfk, hfaith, hX, hX'⟩ := burnsideC137_s6Marking hk N hXeq
  have hfk' : ∀ w : IntMod U hU, f w = 1 ↔ w.val ∈ U ⊓ centralizer (L : Set G) := by
    intro w
    rw [hfk, mem_fixV_autI hU hLU w]
    exact ⟨fun h1 => ⟨w.val_mem, h1⟩, fun h1 => h1.2⟩
  have hS6 : Nonempty (↥(autOn X V) ≃* Equiv.Perm (Fin 6)) := by
    have e1 : Equiv.Perm (Fin 6) ≃* ↥(autI hU X) :=
      (MonoidHom.ofInjective N.ρ_inj).trans (MulEquiv.subgroupCongr (by
        rw [← hXeq, MonoidHom.range_eq_map]))
    exact ⟨((burnsideC137_autIEquiv hU hV hXU hXV hC).symm.trans e1.symm)⟩
  have hmem : ∀ x : ↥X, convHom hU X hXU x ∈ autI hU X := fun x => by
    rw [← range_convHom hU X hXU]
    exact ⟨x, rfl⟩
  have hnat : InternalS6Natural X V U (U ⊓ centralizer (L : Set G)) := by
    refine burnsideC137_ims_of_marking burnsideC137_hDsp burnsideC137_hDsp_injective hU
      inf_le_left hUV hXU hXZ hC f hfs hfk' (fun x hx => hfaith _ (hmem x) hx)
      (fun x => hX _ (hmem x)) fun δ => ?_
    obtain ⟨φ, hφ, hφδ⟩ := hX' δ
    rw [← range_convHom hU X hXU] at hφ
    obtain ⟨x, rfl⟩ := hφ
    exact ⟨x, hφδ⟩
  have hidx : (U ⊓ centralizer (L : Set G)).relIndex U = 2 ^ 4 := by
    rw [burnsideC137_relIndex_of_surj hU f hfs hfk', burnsideC137_card_Dsp]
    norm_num
  have hirrX : IsIrrSection X (U ⊓ centralizer (L : Set G)) U :=
    burnsideC137_isIrrSection_of_isIrrSec hU hLX hXU hXL hirr
  obtain ⟨⟨l, hZl, hlU, hcardl, hPl'⟩, hhat, A, hA, hA2⟩ := hw
  have hidxl : (U ⊓ centralizer (L : Set G)).relIndex l = 4 := by
    have h1 := Subgroup.relIndex_mul_card (U ⊓ centralizer (L : Set G)) l
    rw [inf_eq_left.2 hZl, hcardl] at h1
    have hpos : 0 < Nat.card ↥(U ⊓ centralizer (L : Set G)) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  have hXl : ¬ X ≤ normalizer (l : Set G) := by
    intro hXl
    rcases hirrX.2.2.2 l hZl hlU hXl with h2 | h2
    · rw [← h2, Subgroup.relIndex_self] at hidxl
      omega
    · rw [h2] at hidxl
      rw [hidxl] at hidx
      norm_num at hidx
  have hAV : Nat.card ↥(autOn A V) = Nat.card ↥(autOn A U) := by
    have hAX : A ≤ X := hA.1.trans hTX
    rw [card_autOn_eq_relIndex (hAX.trans hXV), card_autOn_eq_relIndex (hAX.trans hXU)]
    have hAC : A ⊓ centralizer (U : Set G) = A ⊓ centralizer (V : Set G) := by
      have h1 : A ⊓ (X ⊓ centralizer (U : Set G)) = A ⊓ (X ⊓ centralizer (V : Set G)) := by
        rw [hC]
      rwa [← inf_assoc, inf_eq_left.2 hAX, ← inf_assoc, inf_eq_left.2 hAX] at h1
    rw [hAC]
  exact ⟨hS6, hnat, hidx, hirrX, ⟨l, hZl, hlU, hidxl, hPl l hZl hlU hPl' hXl⟩, hhat, A, hA,
    hAV ▸ hA2⟩

theorem burnsideC137_sup_eq_of_index_three [Finite G] {P M D : Subgroup G} (hPM : P ≤ M)
    (hDM : D ≤ M) (h3 : P.relIndex M = 3) (hDP : ¬ D ≤ P) : P ⊔ D = M := by
  apply le_antisymm (sup_le hPM hDM)
  have h1 := Subgroup.relIndex_mul_relIndex P (P ⊔ D) M le_sup_left (sup_le hPM hDM)
  rw [h3] at h1
  have h2 : P.relIndex (P ⊔ D) ≠ 1 := fun h1' =>
    hDP (le_sup_right.trans (Subgroup.relIndex_eq_one.1 h1'))
  have hd : P.relIndex (P ⊔ D) ∣ 3 := ⟨_, h1.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h4 | h4
  · exact absurd h4 h2
  · rw [h4] at h1
    have : (P ⊔ D).relIndex M = 1 := by omega
    exact Subgroup.relIndex_eq_one.1 this

theorem burnsideC137_le_normalizer_of_le {D U l : Subgroup G}
    (hD : D ≤ centralizer (U : Set G)) (hlU : l ≤ U) : D ≤ normalizer (l : Set G) :=
  (hD.trans (Subgroup.centralizer_le hlU)).trans (Subgroup.centralizer_le_normalizer _)

end CFSG.ASVolI
