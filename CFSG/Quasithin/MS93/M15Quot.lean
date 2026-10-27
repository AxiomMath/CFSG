module

public import CFSG.Quasithin.MS93.M15Statement
public import CFSG.Quasithin.MS93.FFStatement
public import CFSG.Quasithin.Background.B5Sec
public import CFSG.Quasithin.Background.SmithB51SL3Coord
public import CFSG.Quasithin.Background.A3Structure312Iso

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] [Finite V] {X K : Subgroup (MulAut V)}

namespace MS15Hyp

theorem conj_mem (h : MS15Hyp X K) {x k : MulAut V} (hx : x ∈ X) (hk : k ∈ K) :
    x * k * x⁻¹ ∈ K :=
  (Subgroup.mem_normalizer_iff.mp (h.le_normalizer hx) k).mp hk

theorem fixV_inv (h : MS15Hyp X K) {x : MulAut V} (hx : x ∈ X) {v : V} (hv : v ∈ fixV K) :
    x v ∈ fixV K :=
  B1Red.fixV_inv_of_normalizes (fun _ hb _ hk => h.conj_mem hb hk) x hx v hv

theorem le_stabSub (h : MS15Hyp X K) : X ≤ stabSub (fixV K) := by
  intro x hx v
  refine ⟨fun hv => ?_, fun hv => h.fixV_inv hx hv⟩
  have := h.fixV_inv (X.inv_mem hx) hv
  simpa using this

omit [Finite V] in
theorem le_stabSub_top (Y : Subgroup (MulAut V)) : Y ≤ stabSub (⊤ : Subgroup V) :=
  fun _ _ _ => Iff.rfl

theorem quasisimple_open (h : MS15Hyp X K) : CFSG.Open.IsQuasisimple ↥K :=
  B1Red.isQuasisimple_to_open h.quasisimple

theorem not_le_centSec (h : MS15Hyp X K) : ¬ K ≤ centSec ⊤ (fixV K) := by
  intro hK
  have hKo := h.quasisimple_open
  have hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    intro a ha b hb
    have hc : ∀ g ∈ K, ∀ v : V, g v * v⁻¹ ∈ fixV K := fun g hg v =>
      (mem_centSec.1 (hK hg)).2 v (Subgroup.mem_top v)
    refine MulEquiv.ext fun v => ?_
    obtain ⟨ca, hca, hav⟩ : ∃ c ∈ fixV K, a v = c * v :=
      ⟨a v * v⁻¹, hc a ha v, by rw [inv_mul_cancel_right]⟩
    obtain ⟨cb, hcb, hbv⟩ : ∃ c ∈ fixV K, b v = c * v :=
      ⟨b v * v⁻¹, hc b hb v, by rw [inv_mul_cancel_right]⟩
    show a (b v) = b (a v)
    rw [hbv, hav, map_mul, map_mul, (mem_fixV.1 hca) b hb, (mem_fixV.1 hcb) a ha, hav, hbv,
      mul_left_comm]
  have hbot : ⁅K, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcomm b hb a ha
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp h.quasisimple.1
  have : Nontrivial ↥K := CFSG.ComponentClassification.Quasisimple.nontrivial hKo
  rw [hperf] at hbot
  exact (Subgroup.nontrivial_iff_ne_bot K).1 this hbot

theorem odd_orderOf (h : MS15Hyp X K) {c : MulAut V} (hc : c ∈ X)
    (hck : ∀ k ∈ K, c * k = k * c) : Odd (orderOf c) := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hcm : c ^ m = 1 := by
    refine h.cent _ (X.pow_mem hc m) (fun l hl => ((Commute.pow_left (hck l hl) m)).eq) k ?_
    rw [← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
  exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hcm)

omit [Finite V] in
theorem conj_mem_centSec {C : Subgroup V} {g x : MulAut V} (hg : g ∈ stabSub C)
    (hx : x ∈ centSec ⊤ C) : g * x * g⁻¹ ∈ centSec ⊤ C := by
  refine ⟨fun _ => Iff.rfl, fun w _ => ?_⟩
  have h1 : x (g⁻¹ w) * (g⁻¹ w)⁻¹ ∈ C := (mem_centSec.1 hx).2 _ (Subgroup.mem_top _)
  have h2 : g (x (g⁻¹ w) * (g⁻¹ w)⁻¹) ∈ C := ((hg _).2 h1)
  have e : (g * x * g⁻¹) w * w⁻¹ = g (x (g⁻¹ w) * (g⁻¹ w)⁻¹) := by
    rw [map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
  rw [e]
  exact h2

theorem faithful (hV : ∀ v : V, v ^ 2 = 1) (h : MS15Hyp X K) :
    X ⊓ centSec ⊤ (fixV K) = ⊥ := by
  set N := X ⊓ centSec ⊤ (fixV K) with hN
  have hNK : ∀ n ∈ N, ∀ k ∈ K, n * k * n⁻¹ ∈ K := fun n hn k hk => h.conj_mem hn.1 hk
  have hKN : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N := fun k hk n hn =>
    ⟨X.mul_mem (X.mul_mem (h.le hk) hn.1) (X.inv_mem (h.le hk)),
      conj_mem_centSec (h.le_stabSub (h.le hk)) hn.2⟩
  have hnot : ¬ K ≤ N := fun hle => h.not_le_centSec (hle.trans inf_le_right)
  have hcomm := B1Red.commute_of_normal_not_le h.quasisimple_open hNK hKN hnot
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have hodd := h.odd_orderOf hn.1 (hcomm n hn)
  set Y := Subgroup.zpowers n with hYdef
  have hY : Odd (Nat.card Y) := by rw [Nat.card_zpowers]; exact hodd
  obtain ⟨hdec, -⟩ := B1.coprime_decomp hV hY (M := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)
  have hYc : commSub ⊤ Y ≤ fixV K := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨y, hy, w, -, rfl⟩
    have hyN : y ∈ centSec ⊤ (fixV K) := (Subgroup.zpowers_le.2 hn.2) hy
    exact (mem_centSec.1 hyN).2 w (Subgroup.mem_top w)
  have hYK : ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y := by
    intro y hy k hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (hcomm n hn k hk) j).eq
  have hfixY : ∀ k ∈ K, ∀ v ∈ fixV Y, k v ∈ fixV Y := by
    intro k hk v hv y hy
    have e : y (k v) = k (y v) := by
      rw [← MulAut.mul_apply, hYK y hy k hk, MulAut.mul_apply]
    rw [e, (mem_fixV.1 hv) y hy]
  have htop : commV K ≤ fixV Y := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨k, hk, v, rfl⟩
    have hv : v ∈ (⊤ ⊓ fixV Y) ⊔ commSub ⊤ Y := by rw [hdec]; exact Subgroup.mem_top v
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hv
    have hkb : k b = b := (mem_fixV.1 (hYc hb)) k hk
    have e : k (a * b) * (a * b)⁻¹ = k a * a⁻¹ := by
      rw [map_mul, hkb, mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
    rw [e]
    exact (fixV Y).mul_mem (hfixY k hk a ha.2) ((fixV Y).inv_mem ha.2)
  refine MulEquiv.ext fun v => ?_
  have hv : v ∈ fixV Y := htop (by rw [h.comm]; exact Subgroup.mem_top v)
  exact (mem_fixV.1 hv) n (Subgroup.mem_zpowers n)

end MS15Hyp

section General

omit [Finite V] in
theorem xmodCommOf_top_eq (X : Subgroup (MulAut V)) :
    XMod.commOf ↥X (⊤ : Subgroup V) = commV X := by
  unfold XMod.commOf commV
  congr 1
  ext w
  constructor
  · rintro ⟨a, l, -, rfl⟩
    exact ⟨a, a.2, l, rfl⟩
  · rintro ⟨x, hx, v, rfl⟩
    exact ⟨⟨x, hx⟩, v, Subgroup.mem_top _, rfl⟩


omit [Finite V] in
theorem le_normalizer_of_conj' {H N : Subgroup (MulAut V)}
    (hc : ∀ g ∈ H, ∀ x ∈ N, g * x * g⁻¹ ∈ N) : H ≤ Subgroup.normalizer (N : Set (MulAut V)) :=
  fun g hg => Subgroup.mem_normalizer_iff.2 fun x => ⟨hc g hg x, fun hx => by
    have h1 := hc g⁻¹ (H.inv_mem hg) _ hx
    rwa [inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h1⟩

theorem isRankTwoLie2Derived_of_mulEquiv {Y₁ Y₂ : Type} [Group Y₁] [Group Y₂] (e : Y₁ ≃* Y₂)
    (h : IsRankTwoLie2Derived Y₁) : IsRankTwoLie2Derived Y₂ := by
  rcases h with ⟨k, h⟩ | ⟨k, h⟩ | ⟨k, h⟩ | ⟨k, h⟩ | h | ⟨k, h⟩ | h | ⟨k, h⟩ | ⟨k, h⟩ | h
  · exact Or.inl ⟨k, IsPSL.of_mulEquiv e h⟩
  · exact Or.inr (Or.inl ⟨k, IsPSU.of_mulEquiv e h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨k, IsPSU.of_mulEquiv e h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, IsPSp4.of_mulEquiv e h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (IsAlt.of_mulEquiv e h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, IsG2.of_mulEquiv e h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (IsPSU.of_mulEquiv e h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨k, Is3D4.of_mulEquiv e h⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨k, Is2F4.of_mulEquiv e h⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (IsTits.of_mulEquiv e h)))))))))

omit [Finite V] in
theorem submoduleClosure_inv {W : Type} [CommGroup W] {Y : Subgroup (MulAut W)} {U : Subgroup W}
    {y : MulAut W} (hy : y ∈ Y) {w : W} (hw : w ∈ G6.submoduleClosure Y U) :
    y w ∈ G6.submoduleClosure Y U := by
  have hle : (G6.submoduleClosure Y U).map y.toMonoidHom ≤ G6.submoduleClosure Y U := by
    rw [G6.submoduleClosure, Subgroup.map_iSup]
    refine iSup_le fun g => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hg => ?_
    rw [Subgroup.map_map]
    have e : y.toMonoidHom.comp (g : MulAut W).toMonoidHom = (y * g).toMonoidHom :=
      MonoidHom.ext fun _ => rfl
    rw [e]
    exact le_iSup₂_of_le (f := fun g (_ : g ∈ Y) => U.map (g : MulAut W).toMonoidHom) (y * g)
      (Y.mul_mem hy hg) le_rfl
  exact hle ⟨w, hw, rfl⟩

omit [Finite V] in
theorem le_submoduleClosure {W : Type} [CommGroup W] (Y : Subgroup (MulAut W)) (U : Subgroup W) :
    U ≤ G6.submoduleClosure Y U := by
  intro u hu
  have h1 : U.map (1 : MulAut W).toMonoidHom ≤ G6.submoduleClosure Y U :=
    le_iSup₂_of_le (f := fun g (_ : g ∈ Y) => U.map (g : MulAut W).toMonoidHom) 1 Y.one_mem le_rfl
  exact h1 ⟨u, hu, rfl⟩

end General

namespace MS15Hyp

variable (hV : ∀ v : V, v ^ 2 = 1) (h : MS15Hyp X K)
include hV h

theorem faithful_le {L : Subgroup (MulAut V)} (hLX : L ≤ X) : L ⊓ centSec ⊤ (fixV K) = ⊥ :=
  le_bot_iff.1 ((inf_le_inf_right _ hLX).trans (h.faithful hV).le)

omit [Finite V] h in
theorem sec_sq (v : Sec (⊤ : Subgroup V) (fixV K)) : v ^ 2 = 1 := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective v
  rw [← QuotientGroup.mk_pow]
  have : w ^ 2 = 1 := Subtype.ext (by simpa using hV (w : V))
  rw [this, QuotientGroup.mk_one]

theorem secHom_injective :
    Function.Injective (B5.secHom X (le_stabSub_top X) h.le_stabSub) :=
  (MonoidHom.ker_eq_bot_iff _).1 (B5.ker_secHom_eq_bot X _ _ (h.faithful hV))

omit hV in
theorem mem_autSec_iff {L : Subgroup (MulAut V)} (hLX : L ≤ X) {y : MulAut (Sec ⊤ (fixV K))} :
    y ∈ autSec L ⊤ (fixV K) ↔
      ∃ x : ↥X, (x : MulAut V) ∈ L ∧ B5.secHom X (le_stabSub_top X) h.le_stabSub x = y := by
  rw [← B5.map_secHom_eq_autSec X (le_stabSub_top X) h.le_stabSub hLX, Subgroup.mem_map]
  exact ⟨fun ⟨x, hx, hxy⟩ => ⟨x, hx, hxy⟩, fun ⟨x, hx, hxy⟩ => ⟨x, hx, hxy⟩⟩

omit hV in
theorem isIrrSec_quot :
    XMod.IsIrrSec ↥(autSec K ⊤ (fixV K)) (⊥ : Subgroup (Sec ⊤ (fixV K))) ⊤ :=
  B5.isIrrSec_autSec h.irr.1 (fun J hJ hCJ hJW => h.irr.2 J (fun a l hl => hJ a a.2 l hl) hCJ hJW)
    (le_stabSub_top K) (h.le.trans h.le_stabSub)

noncomputable def kEquiv : ↥K ≃* ↥(autSec K ⊤ (fixV K)) :=
  B5.secEquiv K (le_stabSub_top K) (h.le.trans h.le_stabSub) (h.faithful_le hV h.le)

theorem fixV_quot_eq_bot : fixV (autSec K ⊤ (fixV K)) = ⊥ := by
  have hinv : XMod.IsInv ↥(autSec K ⊤ (fixV K)) (fixV (autSec K ⊤ (fixV K))) :=
    fun a l hl => by
      show (a : MulAut _) l ∈ _
      rw [(mem_fixV.1 hl) a a.2]
      exact hl
  rcases h.isIrrSec_quot.2 _ hinv bot_le le_top with h0 | h1
  · exact h0
  · exfalso
    have hKbar : autSec K ⊤ (fixV K) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      refine MulEquiv.ext fun v => ?_
      have hv : v ∈ fixV (autSec K ⊤ (fixV K)) := by rw [h1]; trivial
      exact (mem_fixV.1 hv) y hy
    have hK1 : Nontrivial ↥K :=
      CFSG.ComponentClassification.Quasisimple.nontrivial h.quasisimple_open
    have : Nontrivial ↥(autSec K ⊤ (fixV K)) := (kEquiv hV h).symm.toEquiv.nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).1 this hKbar

theorem ffHyp : FFHyp (autSec X ⊤ (fixV K)) (autSec K ⊤ (fixV K)) := by
  set σ := B5.secHom X (le_stabSub_top X) h.le_stabSub with hσ
  have hσi := h.secHom_injective hV
  have hX : ∀ {y}, y ∈ autSec X ⊤ (fixV K) ↔ ∃ x : ↥X, σ x = y := fun {y} => by
    rw [h.mem_autSec_iff le_rfl]
    exact ⟨fun ⟨x, _, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, x.2, hx⟩⟩
  have hK : ∀ {y}, y ∈ autSec K ⊤ (fixV K) ↔ ∃ x : ↥X, (x : MulAut V) ∈ K ∧ σ x = y :=
    fun {y} => h.mem_autSec_iff h.le
  have hKX : autSec K ⊤ (fixV K) ≤ autSec X ⊤ (fixV K) := autSec_mono h.le ⊤ (fixV K)
  have hfK := h.faithful_le hV h.le
  refine ⟨hKX, ?_, B5.isQuasisimple_autSec (le_stabSub_top K) (h.le.trans h.le_stabSub) hfK
    h.quasisimple, B5.sqtk_autSec (le_stabSub_top K) (h.le.trans h.le_stabSub) hfK h.sqtk, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine le_normalizer_of_conj' fun g hg z hz => ?_
    obtain ⟨x, rfl⟩ := hX.1 hg
    obtain ⟨k, hk, rfl⟩ := hK.1 hz
    refine hK.2 ⟨x * k * x⁻¹, h.conj_mem x.2 hk, ?_⟩
    rw [map_mul, map_mul, map_inv]
  ·
    exact isRankTwoLie2Derived_of_mulEquiv
      (QuotientGroup.congr _ _ (kEquiv hV h) (Subgroup.map_center_eq (kEquiv hV h))) h.rankTwo
  ·
    intro c hc hck e hce
    obtain ⟨x, rfl⟩ := hX.1 hc
    have hxk : ∀ k ∈ K, (x : MulAut V) * k = k * x := by
      intro k hk
      have h1 := hck (σ ⟨k, h.le hk⟩) (hK.2 ⟨⟨k, h.le hk⟩, hk, rfl⟩)
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (hσi h1)
    have hx1 : (x : MulAut V) ^ 2 ^ e = 1 := by
      rw [← map_pow] at hce
      have := hσi (hce.trans (map_one σ).symm)
      exact congrArg Subtype.val this
    have : x = 1 := Subtype.ext (h.cent x x.2 hxk e hx1)
    rw [this, map_one]
  ·
    intro y hy
    obtain ⟨x, rfl⟩ := hX.1 hy
    obtain ⟨e, he⟩ := h.two x x.2
    exact ⟨e, hK.2 ⟨x ^ 2 ^ e, he, map_pow σ x _⟩⟩
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨T, hT, -⟩ := A4.exists_isSylowTwoOf_ge (bot_le : ⊥ ≤ autSec K ⊤ (fixV K))
      IsPGroup.of_bot
    refine ⟨T, hT, ?_⟩
    have hirr := h.isIrrSec_quot
    obtain ⟨m, -, hm1, hmfix⟩ := B1.exists_fixed_ne_one (sec_sq hV) hT.2.1
      (M := ⊤) (fun _ _ _ _ => Subgroup.mem_top _) (ne_bot_of_gt hirr.1)
    have hinv : XMod.IsInv ↥(autSec K ⊤ (fixV K))
        (G6.submoduleClosure (autSec X ⊤ (fixV K)) (fixV T)) :=
      fun a l hl => submoduleClosure_inv (hKX a.2) hl
    rcases hirr.2 _ hinv bot_le le_top with h0 | h1
    · exfalso
      have : m ∈ G6.submoduleClosure (autSec X ⊤ (fixV K)) (fixV T) :=
        le_submoduleClosure _ _ (fun b hb => hmfix b hb)
      rw [h0, Subgroup.mem_bot] at this
      exact hm1 this
    · exact h1
  ·
    rw [eq_bot_iff, ← h.fixV_quot_eq_bot hV]
    exact fun v hv x hx => hv x (hKX hx)
  ·
    obtain ⟨A, hAX, hA1, hAe, hcard⟩ := h.ff
    have hAW : A ≤ stabSub (⊤ : Subgroup V) := le_stabSub_top A
    have hAC : A ≤ stabSub (fixV K) := hAX.trans h.le_stabSub
    have hfA := h.faithful_le hV hAX
    have hcA : Nat.card (autSec A ⊤ (fixV K)) = Nat.card A := by
      have := card_autSec_mul hAW hAC
      rwa [hfA, Subgroup.card_bot, mul_one] at this
    have hfix : Nat.card (fixV (autSec A ⊤ (fixV K))) * Nat.card (fixV K) =
        Nat.card (fixQuot A (fixV K)) := by
      have e : B5.fixSec A ⊤ (fixV K) = fixQuot A (fixV K) := by
        ext v
        exact ⟨fun hv => hv.2, fun hv => ⟨Subgroup.mem_top v, hv⟩⟩
      rw [B5.card_fixV_autSec_mul le_top hAW hAC, e]
    have hsec : Nat.card V = Nat.card (Sec (⊤ : Subgroup V) (fixV K)) * Nat.card (fixV K) := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_top : fixV K ≤ ⊤)).toEquiv,
        ← Subgroup.card_eq_card_quotient_mul_card_subgroup, Subgroup.card_top]
    refine ⟨autSec A ⊤ (fixV K), autSec_mono hAX ⊤ (fixV K), ?_, ⟨?_, ?_⟩, ?_⟩
    · intro hbot
      apply hA1
      have h1 : Nat.card A = 1 := by rw [← hcA, hbot, Subgroup.card_bot]
      exact Subgroup.eq_bot_of_card_eq A h1
    · intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := (h.mem_autSec_iff hAX).1 ha
      obtain ⟨y, hy, rfl⟩ := (h.mem_autSec_iff hAX).1 hb
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAe.1 _ hx _ hy)
    · intro a ha
      obtain ⟨x, hx, rfl⟩ := (h.mem_autSec_iff hAX).1 ha
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hAe.2 _ hx)
      rw [this, map_one]
    · have hpos : 0 < Nat.card (fixV K) := Nat.card_pos
      rw [hcA]
      refine Nat.le_of_mul_le_mul_right ?_ hpos
      rw [mul_assoc, hfix, ← hsec]
      exact hcard


theorem realizes_of_quot {L : Subgroup (MulAut V)} (hLX : L ≤ X) {D : FFModel}
    (hD : D.Realizes (autSec L ⊤ (fixV K)) ⊤ ⊥) : D.Realizes L ⊤ (fixV K) := by
  obtain ⟨π, hπ⟩ := hD
  exact ⟨_, B5.realizesVia_of_autSec le_top (le_stabSub_top L) (hLX.trans h.le_stabSub)
    (h.faithful_le hV hLX) hπ⟩

theorem binaryNaturalSL_of_quot {L : Subgroup (MulAut V)} (hLX : L ≤ X) {d a : ℕ}
    (hD : BinaryNaturalSL (autSec L ⊤ (fixV K)) ⊤ ⊥ d a) : BinaryNaturalSL L ⊤ (fixV K) d a := by
  obtain ⟨F, iF, fF, hF, hR⟩ := hD
  exact ⟨F, iF, fF, hF, h.realizes_of_quot hV hLX hR⟩

theorem binaryNaturalSp4_of_quot {L : Subgroup (MulAut V)} (hLX : L ≤ X) {a : ℕ}
    (hD : BinaryNaturalSp4 (autSec L ⊤ (fixV K)) ⊤ ⊥ a) : BinaryNaturalSp4 L ⊤ (fixV K) a := by
  obtain ⟨F, iF, fF, hF, hR⟩ := hD
  exact ⟨F, iF, fF, hF, h.realizes_of_quot hV hLX hR⟩

theorem alternatingNatural_of_quot {L : Subgroup (MulAut V)} (hLX : L ≤ X) {n : ℕ}
    (hD : AlternatingNatural (autSec L ⊤ (fixV K)) ⊤ ⊥ n) : AlternatingNatural L ⊤ (fixV K) n :=
  h.realizes_of_quot hV hLX hD

theorem g2Natural_of_quot {L : Subgroup (MulAut V)} (hLX : L ≤ X) {a : ℕ}
    (hD : G2Natural (autSec L ⊤ (fixV K)) ⊤ ⊥ a) : G2Natural L ⊤ (fixV K) a := by
  obtain ⟨F, iF, fF, hF, hR⟩ := hD
  exact ⟨F, iF, fF, hF, h.realizes_of_quot hV hLX hR⟩

theorem g2NaturalDerived_of_quot {L : Subgroup (MulAut V)} (hLX : L ≤ X) {a : ℕ}
    (hD : G2NaturalDerived (autSec L ⊤ (fixV K)) ⊤ ⊥ a) :
    G2NaturalDerived L ⊤ (fixV K) a := by
  obtain ⟨F, iF, fF, hF, hR⟩ := hD
  exact ⟨F, iF, fF, hF, h.realizes_of_quot hV hLX hR⟩

theorem tripleA6Six_of_quot {L : Subgroup (MulAut V)} (hLX : L ≤ X)
    (hD : TripleA6Six (autSec L ⊤ (fixV K)) ⊤ ⊥) : TripleA6Six L ⊤ (fixV K) := by
  obtain ⟨F, iF, fF, Γ₀, hF, hdet, hhat, hsc, hR⟩ := hD
  exact ⟨F, iF, fF, Γ₀, hF, hdet, hhat, hsc, h.realizes_of_quot hV hLX hR⟩

omit [Finite V] hV h in
theorem ne_of_quot_ne (hne : autSec X ⊤ (fixV K) ≠ autSec K ⊤ (fixV K)) : X ≠ K := by
  intro hXK
  apply hne
  rw [hXK]

end MS15Hyp

end CFSG.Quasithin.MS93
