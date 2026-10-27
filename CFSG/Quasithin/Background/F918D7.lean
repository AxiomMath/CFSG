module

public import CFSG.Quasithin.EmptyFaithful.F918C13
public import CFSG.Quasithin.EmptyFaithful.F918C11
public import CFSG.Quasithin.Background.F918D2
public import CFSG.Quasithin.Background.F918D4
public import CFSG.Quasithin.Background.F918D5
public import CFSG.Quasithin.Background.F918D6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

structure N4Cfg (W : Type) [CommGroup W] [Finite W] (L : Subgroup (MulAut W)) (V : Subgroup W)
    (σ : MulAut W) (A : Subgroup (MulAut W)) : Prop where
  hexp : ∀ w : W, w ^ 2 = 1
  hinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V
  hcomm : XMod.commOf ↥L V = V
  hnat : BinaryNaturalSL L V (V ⊓ fixV L) 3 1
  hZ : Nat.card ↥(V ⊓ fixV L) = 2
  hσL : ∀ x : MulAut W, x ∈ L ↔ σ * x * σ⁻¹ ∈ L
  hne : V.map σ.toMonoidHom ≠ V
  hdyn : ¬ ∃ l₀ ∈ L, ∀ x ∈ L, (σ * l₀⁻¹) * x = x * (σ * l₀⁻¹)
  hsum : V ⊔ V.map σ.toMonoidHom = ⊤
  hint : V ⊓ V.map σ.toMonoidHom ≤ fixV L
  hAN : ∀ a ∈ A, ∀ x : MulAut W, x ∈ L ↔ a * x * a⁻¹ ∈ L
  hAelem : IsElemAbelian2 A
  hAquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w : W, b (a w * w⁻¹) = a w * w⁻¹
  hAfaith : ∀ a ∈ A, (∀ x ∈ L, a * x = x * a) → a = 1
  hArat : rAV A ≤ 2
  hAne : A ≠ ⊥

section Derive

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem n4_sup_eq_top {M L : Subgroup (MulAut W)} {V : Subgroup W} {σ : MulAut W}
    (hinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V) (hcomm : XMod.commOf ↥L V = V)
    (hσL : ∀ x : MulAut W, x ∈ L ↔ σ * x * σ⁻¹ ∈ L)
    (hsum1 : (⊤ : Subgroup W) = V ⊔ V.map σ.toMonoidHom ⊔ fixV L)
    (hMN : ∀ m ∈ M, ∀ x : MulAut W, x ∈ L ↔ m * x * m⁻¹ ∈ L)
    (hgen : (⨆ m ∈ M, V.map m.toMonoidHom) = ⊤) : V ⊔ V.map σ.toMonoidHom = ⊤ := by
  set U := V ⊔ V.map σ.toMonoidHom with hU
  have hUinv : ∀ x ∈ L, ∀ u ∈ U, x u ∈ U := by
    intro x hx u hu
    obtain ⟨v, hv, v', hv', rfl⟩ := Subgroup.mem_sup.1 hu
    rw [map_mul]
    refine U.mul_mem (Subgroup.mem_sup_left (hinv x hx v hv)) ?_
    obtain ⟨w, hw, rfl⟩ := hv'
    have hx' : σ⁻¹ * x * σ ∈ L := by
      rw [hσL]
      simpa [mul_assoc] using hx
    refine Subgroup.mem_sup_right ⟨(σ⁻¹ * x * σ) w, hinv _ hx' w hw, ?_⟩
    simp [MulAut.mul_apply]
  rw [eq_top_iff, ← hgen]
  refine iSup₂_le fun m hm => ?_
  have h1 : V.map m.toMonoidHom = (XMod.commOf ↥L V).map m.toMonoidHom := by rw [hcomm]
  rw [h1]
  unfold XMod.commOf
  rw [MonoidHom.map_closure]
  refine (Subgroup.closure_le U).2 ?_
  rintro _ ⟨c, ⟨a, l, hl, rfl⟩, rfl⟩
  have hx : m * (a : MulAut W) * m⁻¹ ∈ L := (hMN m hm _).1 a.2
  have hw : m l ∈ (⊤ : Subgroup W) := Subgroup.mem_top _
  rw [hsum1] at hw
  obtain ⟨u, hu, c', hc', hwuc⟩ := Subgroup.mem_sup.1 hw
  have e1 : m.toMonoidHom ((a • l) * l⁻¹) = (m * (a : MulAut W) * m⁻¹) (m l) * (m l)⁻¹ := by
    show m ((a : MulAut W) l * l⁻¹) = _
    simp [MulAut.mul_apply]
  rw [e1, ← hwuc, map_mul, hc' _ hx]
  have : (m * (a : MulAut W) * m⁻¹) u * c' * (u * c')⁻¹ = (m * (a : MulAut W) * m⁻¹) u * u⁻¹ := by
    group
  rw [this]
  exact U.mul_mem (hUinv _ hx u hu) (U.inv_mem hu)

theorem n4_card_eq_two {Z : Subgroup W} (hle : Nat.card ↥Z ≤ 2) (hne : Z ≠ ⊥) : Nat.card ↥Z = 2 := by
  have h1 : 1 < Nat.card ↥Z := (Subgroup.one_lt_card_iff_ne_bot Z).2 hne
  omega

theorem N4Cfg.of_hyps {M Mp T L A : Subgroup (MulAut W)}
    {V : Subgroup W} {σ : MulAut W} (hstd : D3Std M Mp T L V) (hMp : Mp = L)
    (hA : QOff Mp T A (orbSup T V)) 
    (hσN : σ ∈ Subgroup.normalizer (L : Set (MulAut W))) (hdyn : ModDynkin L σ)
    (hσV : σ ∉ stabSub V) (hsum : IsSumMod (fixV L) V (V.map σ.toMonoidHom) ⊤)
    (hPSL : IsPSL 3 2 1 ↥L) (hnat : BinaryNaturalSL L V (V ⊓ fixV L) 3 1)
    (hZne : V ⊓ fixV L ≠ ⊥) : N4Cfg W L V σ A := by
  subst hMp
  have hD := hstd.hyp
  have hirr := hD.irr
  have hinv : ∀ x ∈ Mp, ∀ v ∈ V, x v ∈ V := fun x hx v hv => hirr.2.1 ⟨x, hx⟩ v hv
  have hcomm : XMod.commOf ↥Mp V = V := hirr.2.2.1
  have hexp := hD.exp
  have hZ := n4_card_eq_two (card_fixV_le_two_of_natural3 hexp Mp V hinv hcomm hnat) hZne
  have hσL : ∀ x : MulAut W, x ∈ Mp ↔ σ * x * σ⁻¹ ∈ Mp := Subgroup.mem_normalizer_iff.1 hσN
  have hMN : ∀ m ∈ M, ∀ x : MulAut W, x ∈ Mp ↔ m * x * m⁻¹ ∈ Mp := fun m hm =>
    Subgroup.mem_normalizer_iff.1 (hD.Mp_normal hm)
  have hdyn' : ¬ ∃ l₀ ∈ Mp, ∀ x ∈ Mp, (σ * l₀⁻¹) * x = x * (σ * l₀⁻¹) := by
    rcases hdyn with ⟨-, hout⟩ | ⟨hAlt, -⟩
    · exact hout
    · exfalso
      obtain ⟨e⟩ := hAlt
      have h1 : Nat.card ↥Mp = Nat.card ↥(alternatingGroup (Fin 6)) := Nat.card_congr e.toEquiv
      have h2 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
        rw [nat_card_alternatingGroup]
        simp [Nat.factorial]
      have h3 := card_eq_168_of_isPSL_three_two hPSL
      omega
  have hne : V.map σ.toMonoidHom ≠ V := by
    intro h
    apply hσV
    intro u
    have h1 : σ u ∈ V.map σ.toMonoidHom ↔ u ∈ V := Subgroup.mem_map_iff_mem σ.injective
    rw [h] at h1
    exact h1
  have hsum' : V ⊔ V.map σ.toMonoidHom = ⊤ :=
    n4_sup_eq_top hinv hcomm hσL hsum.1 hMN hD.gen
  have hint : V ⊓ V.map σ.toMonoidHom ≤ fixV Mp := by
    intro x hx
    exact hsum.2 ⟨Subgroup.mem_sup_left hx.1, Subgroup.mem_sup_left hx.2⟩
  have hTM : T ≤ M := hD.sylow.1
  refine ⟨hexp, hinv, hcomm, hnat, hZ, hσL, hne, hdyn', hsum', hint, ?_, hA.elem, ?_, hA.faithMp,
    hA.rat, hA.ne⟩
  · intro a ha
    exact hMN a (hTM (hA.le ha))
  · intro a ha b hb w
    have h2 : commSeries A 2 = ⊥ := hA.quad
    have h3 : a w * w⁻¹ ∈ commSub (⊤ : Subgroup W) A :=
      Subgroup.subset_closure ⟨a, ha, w, Subgroup.mem_top w, rfl⟩
    have h4 : b (a w * w⁻¹) * (a w * w⁻¹)⁻¹ ∈ commSub (commSub (⊤ : Subgroup W) A) A :=
      Subgroup.subset_closure ⟨b, hb, _, h3, rfl⟩
    have h5 : commSub (commSub (⊤ : Subgroup W) A) A = ⊥ := h2
    rw [h5, Subgroup.mem_bot] at h4
    exact mul_inv_eq_one.1 h4

end Derive

namespace N4Core

section AutHelpers

variable {W : Type} [CommGroup W]

theorem map_mul_aut (a b : MulAut W) (U : Subgroup W) :
    U.map (a * b).toMonoidHom = (U.map b.toMonoidHom).map a.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem map_one_aut (U : Subgroup W) : U.map (1 : MulAut W).toMonoidHom = U := by
  ext x
  simp

theorem map_inv_of_map_eq {V : Subgroup W} {b : MulAut W} (hb : V.map b.toMonoidHom = V) :
    V.map b⁻¹.toMonoidHom = V := by
  have h1 := map_mul_aut b⁻¹ b V
  rw [inv_mul_cancel, map_one_aut, hb] at h1
  exact h1.symm

theorem mem_iff_of_map_eq {V : Subgroup W} {g : MulAut W} (hg : V.map g.toMonoidHom = V) (v : W) :
    g v ∈ V ↔ v ∈ V := by
  have h1 : g v ∈ V.map g.toMonoidHom ↔ v ∈ V := Subgroup.mem_map_iff_mem g.injective
  rw [hg] at h1
  exact h1

theorem zpow_sq_eq {G : Type*} [Group G] {b : G} (hb : b ^ 2 = 1) (k : ℤ) :
    b ^ k = 1 ∨ b ^ k = b := by
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul]
    simp [hb]
  · right
    rw [zpow_add_one, zpow_mul]
    simp [hb]

theorem isInvol_of {L : Subgroup (MulAut W)} (e : L3.Γ ≃* ↥L) {p : MulAut W} (hp : p ∈ L) (hp1 : p ≠ 1) (hp2 : p ^ 2 = 1) :
    L3.IsInvol (e.symm ⟨p, hp⟩) := by
  constructor
  · apply e.injective
    simp only [map_mul, map_one, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    simpa [pow_two] using hp2
  · intro h1
    apply hp1
    have := congrArg (fun γ => ((e γ : ↥L) : MulAut W)) h1
    simpa using this

end AutHelpers

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} {V : Subgroup W}
  {σ : MulAut W} {A : Subgroup (MulAut W)} (h : N4Cfg W L V σ A)
include h

theorem uni (S : Subgroup W) (hSV : S ≤ V) (hS : ∀ x ∈ L, ∀ s ∈ S, x s ∈ S) :
    S = ⊥ ∨ S = V ⊓ fixV L ∨ S = V :=
  cover_uniserial h.hexp L V h.hinv h.hcomm h.hnat h.hZ S hSV hS

theorem perm {g : MulAut W} (hg : ∀ x : MulAut W, x ∈ L ↔ g * x * g⁻¹ ∈ L) :
    V.map g.toMonoidHom = V ∨ V.map g.toMonoidHom = V.map σ.toMonoidHom :=
  cover_map_eq_or h.hexp L V h.hinv h.hcomm h.hnat h.hZ (fun S hSV hS => uni h S hSV hS) σ h.hσL
    h.hne h.hdyn h.hsum h.hint g hg

theorem faithV {l : MulAut W} (hl : l ∈ L) (hv : ∀ v ∈ V, l v = v) : l = 1 :=
  cover_faithful h.hexp L V h.hinv h.hcomm h.hnat h.hZ l hl hv

theorem commSub_card {l : MulAut W} (hl : l ∈ L) (h1 : l ≠ 1) (h2 : l ^ 2 = 1) :
    Nat.card ↥(commSub V (Subgroup.zpowers l)) = 4 ∧
      commSub V (Subgroup.zpowers l) = V ⊓ fixV (Subgroup.zpowers l) :=
  cover_commSub_involution h.hexp L V h.hinv h.hcomm h.hnat h.hZ l hl h1 h2

theorem act_of_stab {g : MulAut W} (hgL : ∀ x : MulAut W, x ∈ L ↔ g * x * g⁻¹ ∈ L)
    (hg : V.map g.toMonoidHom = V) : ∃ l ∈ L, ∀ v ∈ V, g v = l v :=
  cover_normalizer_stab h.hexp L V h.hinv h.hcomm h.hnat h.hZ g hgL (mem_iff_of_map_eq hg)

theorem sigma_conj_mem (z : MulAut W) : σ⁻¹ * z * σ ∈ L ↔ z ∈ L := by
  rw [h.hσL (σ⁻¹ * z * σ)]
  simp [mul_assoc]

theorem stab_sigma {b : MulAut W} (hb : b ∈ A) (hbV : V.map b.toMonoidHom = V) :
    (V.map σ.toMonoidHom).map b.toMonoidHom = V.map σ.toMonoidHom := by
  have hbσ : ∀ x : MulAut W, x ∈ L ↔ (b * σ) * x * (b * σ)⁻¹ ∈ L := by
    intro x
    rw [h.hσL x, h.hAN b hb (σ * x * σ⁻¹)]
    simp [mul_assoc]
  rcases perm h hbσ with h1 | h1
  · exfalso
    apply h.hne
    rw [map_mul_aut] at h1
    have h2 : ((V.map σ.toMonoidHom).map b.toMonoidHom).map b⁻¹.toMonoidHom =
        V.map σ.toMonoidHom := by
      rw [← map_mul_aut, inv_mul_cancel, map_one_aut]
    rw [h1] at h2
    rw [← h2, map_inv_of_map_eq hbV]
  · rw [map_mul_aut] at h1
    exact h1

theorem conj_eq_of_act {g l : MulAut W} (hgL : ∀ x : MulAut W, x ∈ L ↔ g * x * g⁻¹ ∈ L)
    (hl : l ∈ L) (hgl : ∀ v ∈ V, g v = l v) :
    ∀ x ∈ L, g * x * g⁻¹ = l * x * l⁻¹ := by
  intro x hx
  have hx1 : g * x * g⁻¹ ∈ L := (hgL x).1 hx
  have hx2 : l * x * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl)
  have hinvV : ∀ v ∈ V, g⁻¹ v = l⁻¹ v := by
    intro v hv
    have h1 : l⁻¹ v ∈ V := h.hinv _ (L.inv_mem hl) v hv
    have h2 : g (l⁻¹ v) = v := by rw [hgl _ h1]; simp
    calc g⁻¹ v = g⁻¹ (g (l⁻¹ v)) := by rw [h2]
      _ = l⁻¹ v := by simp
  have h3 : (g * x * g⁻¹)⁻¹ * (l * x * l⁻¹) = 1 := by
    apply faithV h (L.mul_mem (L.inv_mem hx1) hx2)
    intro v hv
    have h4 : x (l⁻¹ v) ∈ V := h.hinv _ hx _ (h.hinv _ (L.inv_mem hl) v hv)
    have h5 : (g * x * g⁻¹) v = (l * x * l⁻¹) v := by
      simp only [MulAut.mul_apply]
      rw [hinvV v hv, hgl _ h4]
    have h6 : (g * x * g⁻¹)⁻¹ ((l * x * l⁻¹) v) = v := by
      rw [← h5]; simp
    simpa [MulAut.mul_apply] using h6
  exact inv_mul_eq_one.1 h3

theorem stab_mem_L {b : MulAut W} (hb : b ∈ A) (hbV : V.map b.toMonoidHom = V) : b ∈ L := by
  obtain ⟨l, hl, hbl⟩ := act_of_stab h (h.hAN b hb) hbV
  have hbVσ := stab_sigma h hb hbV
  have hg'L : ∀ x : MulAut W, x ∈ L ↔ (σ⁻¹ * b * σ) * x * (σ⁻¹ * b * σ)⁻¹ ∈ L := by
    intro x
    have e : (σ⁻¹ * b * σ) * x * (σ⁻¹ * b * σ)⁻¹ = σ⁻¹ * (b * (σ * x * σ⁻¹) * b⁻¹) * σ := by group
    rw [e, sigma_conj_mem h, ← h.hAN b hb (σ * x * σ⁻¹), ← h.hσL x]
  have hg'V : V.map (σ⁻¹ * b * σ).toMonoidHom = V := by
    rw [map_mul_aut, map_mul_aut]
    have : (V.map σ.toMonoidHom).map b.toMonoidHom = V.map σ.toMonoidHom := hbVσ
    rw [this]
    have h2 : (V.map σ.toMonoidHom).map σ⁻¹.toMonoidHom = V := by
      rw [← map_mul_aut, inv_mul_cancel, map_one_aut]
    exact h2
  obtain ⟨l', hl', hg'l'⟩ := act_of_stab h hg'L hg'V
  set l'' := σ * l' * σ⁻¹ with hl''
  have hl''L : l'' ∈ L := (h.hσL l').1 hl'
  have hbVσ' : ∀ v ∈ V, b (σ v) = l'' (σ v) := by
    intro v hv
    have h1 := hg'l' v hv
    have e1 : b (σ v) = σ ((σ⁻¹ * b * σ) v) := by simp [MulAut.mul_apply]
    rw [e1, h1]
    simp [hl'', MulAut.mul_apply]
  have hc1 := conj_eq_of_act h (h.hAN b hb) hl hbl
  have hc2 := conj_eq_of_act h hg'L hl' hg'l'
  have hll : l = l'' := by
    have hcomm : ∀ x ∈ L, (l''⁻¹ * l) * x = x * (l''⁻¹ * l) := by
      intro x hx
      have hx' : σ⁻¹ * x * σ ∈ L := (sigma_conj_mem h x).2 hx
      have e1 := hc1 x hx
      have e2 := hc2 (σ⁻¹ * x * σ) hx'
      have e3 : b * x * b⁻¹ = l'' * x * l''⁻¹ := by
        have : σ * ((σ⁻¹ * b * σ) * (σ⁻¹ * x * σ) * (σ⁻¹ * b * σ)⁻¹) * σ⁻¹ = b * x * b⁻¹ := by group
        rw [← this, e2]
        simp only [hl'']
        group
      have e4 : l * x * l⁻¹ = l'' * x * l''⁻¹ := e1.symm.trans e3
      calc (l''⁻¹ * l) * x = l''⁻¹ * (l * x * l⁻¹) * l := by group
        _ = l''⁻¹ * (l'' * x * l''⁻¹) * l := by rw [e4]
        _ = x * (l''⁻¹ * l) := by group
    have h1 : l''⁻¹ * l = 1 :=
      cover_center_trivial h.hexp L V h.hinv h.hcomm h.hnat h.hZ _ (L.mul_mem (L.inv_mem hl''L) hl) hcomm
    exact (inv_mul_eq_one.1 h1).symm
  have hbl_all : ∀ w : W, b w = l w := by
    intro w
    have hw : w ∈ V ⊔ V.map σ.toMonoidHom := by rw [h.hsum]; trivial
    obtain ⟨v, hv, u, hu, rfl⟩ := Subgroup.mem_sup.1 hw
    obtain ⟨v', hv', rfl⟩ := hu
    rw [map_mul, map_mul, hbl v hv]
    have := hbVσ' v' hv'
    show _ = _
    congr 1
    simpa [hll] using this
  have : b = l := MulEquiv.ext hbl_all
  rw [this]
  exact hl

theorem card_V : Nat.card ↥V = 16 := by
  obtain ⟨D⟩ := h.hnat.toL3Coord
  have h1 := Subgroup.card_ker_mul_card_range D.β
  rw [MonoidHom.range_eq_top.2 D.β_surj, Subgroup.card_top] at h1
  have hker : D.β.ker = (V ⊓ fixV L).subgroupOf V := by
    ext u
    rw [MonoidHom.mem_ker, D.ker_β, Subgroup.mem_subgroupOf]
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : V ⊓ fixV L ≤ V)).toEquiv,
    h.hZ] at h1
  have h8 : Nat.card (Multiplicative L3.Vec) = 8 := by
    change Nat.card (Fin 3 → ZMod 2) = 8
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    norm_num
  rw [h8] at h1
  omega

theorem card_comm_nonstab {a : MulAut W} (haV : V.map a.toMonoidHom = V.map σ.toMonoidHom) :
    8 ≤ Nat.card ↥(commV (Subgroup.zpowers a)) := by
  let φ : ↥V →* W :=
    { toFun := fun v => a (v : W) * (v : W)⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        rw [mul_comm ((y : W)⁻¹) ((x : W)⁻¹)]
        exact mul_mul_mul_comm _ _ _ _ }
  have hker : φ.ker ≤ (V ⊓ fixV L).subgroupOf V := by
    intro v hv
    rw [MonoidHom.mem_ker] at hv
    have hav : a (v : W) = v := mul_inv_eq_one.1 hv
    have hvσ : (v : W) ∈ V.map σ.toMonoidHom := by
      rw [← haV]
      exact ⟨v, v.2, hav⟩
    exact Subgroup.mem_subgroupOf.2 ⟨v.2, h.hint ⟨v.2, hvσ⟩⟩
  have hrange : φ.range ≤ commV (Subgroup.zpowers a) := by
    rintro _ ⟨v, rfl⟩
    exact Subgroup.subset_closure ⟨a, Subgroup.mem_zpowers a, v, rfl⟩
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 := card_V h
  have h3 : Nat.card φ.ker ≤ 2 := by
    have := Subgroup.card_le_of_le hker
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : V ⊓ fixV L ≤ V)).toEquiv,
      h.hZ] at this
    exact this
  have h4 : Nat.card φ.range ≤ Nat.card ↥(commV (Subgroup.zpowers a)) :=
    Subgroup.card_le_of_le hrange
  have h5 : 16 ≤ 2 * Nat.card φ.range := by
    calc 16 = Nat.card φ.ker * Nat.card φ.range := by rw [h1, h2]
      _ ≤ 2 * Nat.card φ.range := Nat.mul_le_mul_right _ h3
  omega

theorem card_comm_stab {a : MulAut W} (ha : a ∈ A) (ha1 : a ≠ 1) (haV : V.map a.toMonoidHom = V) :
    8 ≤ Nat.card ↥(commV (Subgroup.zpowers a)) := by
  have haL : a ∈ L := stab_mem_L h ha haV
  have ha2 : a ^ 2 = 1 := h.hAelem.2 a ha
  have hl3L : σ⁻¹ * a * σ ∈ L := (sigma_conj_mem h a).2 haL
  have hl31 : σ⁻¹ * a * σ ≠ 1 := by
    intro h1
    apply ha1
    have h2 : σ * (σ⁻¹ * a * σ) * σ⁻¹ = a := by group
    rw [h1] at h2
    simpa using h2.symm
  have hl32 : (σ⁻¹ * a * σ) ^ 2 = 1 := by
    have : (σ⁻¹ * a * σ) ^ 2 = σ⁻¹ * a ^ 2 * σ := by rw [pow_two, pow_two]; group
    rw [this, ha2]
    group
  obtain ⟨hc1, -⟩ := commSub_card h haL ha1 ha2
  obtain ⟨hc2, -⟩ := commSub_card h hl3L hl31 hl32
  set Y₁ := commSub V (Subgroup.zpowers a) with hY₁def
  set Y₃ := commSub V (Subgroup.zpowers (σ⁻¹ * a * σ)) with hY₃def
  set Y₂ := Y₃.map σ.toMonoidHom with hY₂def
  have hY₁ : Y₁ ≤ commV (Subgroup.zpowers a) :=
    Subgroup.closure_mono (by rintro _ ⟨x, hx, w, hw, rfl⟩; exact ⟨x, hx, w, rfl⟩)
  have hY₁V : Y₁ ≤ V := by
    refine (Subgroup.closure_le V).2 ?_
    rintro _ ⟨x, hx, w, hw, rfl⟩
    have hxL : x ∈ L := (Subgroup.zpowers_le.2 haL) hx
    exact V.mul_mem (h.hinv x hxL w hw) (V.inv_mem hw)
  have hY₃V : Y₃ ≤ V := by
    refine (Subgroup.closure_le V).2 ?_
    rintro _ ⟨x, hx, w, hw, rfl⟩
    have hxL : x ∈ L := (Subgroup.zpowers_le.2 hl3L) hx
    exact V.mul_mem (h.hinv x hxL w hw) (V.inv_mem hw)
  have hY₂ : Y₂ ≤ commV (Subgroup.zpowers a) := by
    rw [hY₂def, hY₃def]
    unfold commSub
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, ⟨x, hx, w, hw, rfl⟩, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine Subgroup.subset_closure ⟨a ^ k, ⟨k, rfl⟩, σ w, ?_⟩
    have e0 : (σ⁻¹ * a * σ) ^ k = σ⁻¹ * a ^ k * σ := by
      simpa using (conj_zpow (a := σ⁻¹) (b := a) (i := k))
    show (a ^ k) (σ w) * (σ w)⁻¹ = σ (((σ⁻¹ * a * σ) ^ k) w * w⁻¹)
    simp [e0, MulAut.mul_apply]
  have hY₂V : Y₂ ≤ V.map σ.toMonoidHom := Subgroup.map_mono hY₃V
  have hcard2 : Nat.card Y₂ = 4 := (Subgroup.card_map_of_injective σ.injective).trans hc2
  by_contra hlt
  push Not at hlt
  have hpow := card_eq_two_pow h.hexp (commV (Subgroup.zpowers a))
  have hge : 4 ≤ Nat.card ↥(commV (Subgroup.zpowers a)) := by
    have := Subgroup.card_le_of_le hY₁
    rw [hc1] at this
    exact this
  have h4 : Nat.card ↥(commV (Subgroup.zpowers a)) = 4 := by
    obtain ⟨r, hr⟩ : ∃ r, Nat.card ↥(commV (Subgroup.zpowers a)) = 2 ^ r := ⟨_, hpow⟩
    have hr2 : r = 2 := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt2 | hgt2
      · have h5 : 2 ^ r ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h6 : (2 : ℕ) ^ 1 = 2 := by norm_num
        omega
      · have h5 : 2 ^ 3 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h6 : (2 : ℕ) ^ 3 = 8 := by norm_num
        omega
    subst hr2
    simpa using hr
  have hQ1 : Y₁ = commV (Subgroup.zpowers a) :=
    Subgroup.eq_of_le_of_card_ge hY₁ (by rw [hc1, h4])
  have hQ2 : Y₂ = commV (Subgroup.zpowers a) :=
    Subgroup.eq_of_le_of_card_ge hY₂ (by rw [hcard2, h4])
  have hle : Y₁ ≤ V ⊓ fixV L := by
    intro y hy
    have hy2 : y ∈ Y₂ := by rw [hQ2, ← hQ1]; exact hy
    exact ⟨hY₁V hy, h.hint ⟨hY₁V hy, hY₂V hy2⟩⟩
  have := Subgroup.card_le_of_le hle
  rw [hc1, h.hZ] at this
  omega

theorem rank_contra {a : MulAut W} (ha : a ∈ A) (ha1 : a ≠ 1) (hA : ∀ b ∈ A, b = 1 ∨ b = a) :
    False := by
  have hQ : 8 ≤ Nat.card ↥(commV (Subgroup.zpowers a)) := by
    rcases perm h (h.hAN a ha) with h1 | h1
    · exact card_comm_stab h ha ha1 h1
    · exact card_comm_nonstab h h1
  have hAeq : A = Subgroup.zpowers a := by
    ext x
    constructor
    · intro hx
      rcases hA x hx with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    · intro hx
      exact (Subgroup.zpowers_le.2 ha) hx
  have ha2 : a ^ 2 = 1 := h.hAelem.2 a ha
  have hcardA : Nat.card ↥A = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [hAeq, Nat.card_zpowers, orderOf_eq_prime ha2 ha1]
  have hrkA : rk ↥A = 1 := by
    unfold rk
    rw [hcardA]
    simp
  have h1 := card_commV_mul_card_fixV h.hexp a
  have hfix : fixV A = fixV (Subgroup.zpowers a) := by rw [hAeq]
  have hr3 : 3 ≤ rkIdx (fixV (Subgroup.zpowers a)) := by
    have e1 := rk_add_rkIdx (fixV (Subgroup.zpowers a))
    have e2 := card_eq_two_pow_top h.hexp
    have e3 := card_eq_two_pow h.hexp (fixV (Subgroup.zpowers a))
    rw [e3, e2] at h1
    have h8 : 8 * 2 ^ rk ↥(fixV (Subgroup.zpowers a)) ≤ 2 ^ rk W := by
      calc 8 * 2 ^ rk ↥(fixV (Subgroup.zpowers a)) ≤
            Nat.card ↥(commV (Subgroup.zpowers a)) * 2 ^ rk ↥(fixV (Subgroup.zpowers a)) :=
            Nat.mul_le_mul_right _ hQ
        _ = 2 ^ rk W := h1
    have h9 : 2 ^ (rk ↥(fixV (Subgroup.zpowers a)) + 3) ≤ 2 ^ rk W := by
      calc 2 ^ (rk ↥(fixV (Subgroup.zpowers a)) + 3) = 8 * 2 ^ rk ↥(fixV (Subgroup.zpowers a)) := by ring
        _ ≤ _ := h8
    have h10 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h9
    omega
  have hrat := h.hArat
  unfold rAV at hrat
  rw [hrkA] at hrat
  rw [hfix] at hrat
  have : (3 : ℚ) ≤ rkIdx (fixV (Subgroup.zpowers a)) := by exact_mod_cast hr3
  simp at hrat
  linarith

theorem pair_contra {τ b : MulAut W} (hτ : τ ∈ A) (hτV : V.map τ.toMonoidHom ≠ V) (hb : b ∈ A)
    (hb1 : b ≠ 1) (hbV : V.map b.toMonoidHom = V) : False := by
  have hτσ : V.map τ.toMonoidHom = V.map σ.toMonoidHom :=
    (perm h (h.hAN τ hτ)).resolve_left hτV
  have hbL := stab_mem_L h hb hbV
  have hb2 : b ^ 2 = 1 := h.hAelem.2 b hb
  obtain ⟨hc, -⟩ := commSub_card h hbL hb1 hb2
  have hle : commSub V (Subgroup.zpowers b) ≤ V ⊓ fixV L := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rcases zpow_sq_eq hb2 k with hk | hk
    · rw [hk]
      simp only [MulAut.one_apply, mul_inv_cancel]
      exact one_mem _
    · rw [hk]
      have hbwV : b w ∈ V := (mem_iff_of_map_eq hbV w).2 hw
      have hu : b w * w⁻¹ ∈ V := V.mul_mem hbwV (V.inv_mem hw)
      have hfix : τ (b w * w⁻¹) = b w * w⁻¹ := h.hAquad b hb τ hτ w
      have huτ : b w * w⁻¹ ∈ V.map τ.toMonoidHom := ⟨_, hu, hfix⟩
      rw [hτσ] at huτ
      exact ⟨hu, h.hint ⟨hu, huτ⟩⟩
  have := Subgroup.card_le_of_le hle
  rw [hc, h.hZ] at this
  omega

omit [Finite W] h in
theorem pi_injective (D : L3Data L V (V ⊓ fixV L)) : Function.Injective D.π := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  apply L3.act_injective
  intro z
  obtain ⟨v, hv⟩ := D.β_surj (Multiplicative.ofAdd z)
  have hv' : ((D.π γ : ↥L) : MulAut W) (v : W) ∈ V := D.inv_U _ (D.π γ).2 _ v.2
  have h1 := D.equi γ v hv'
  have h2 : (⟨((D.π γ : ↥L) : MulAut W) (v : W), hv'⟩ : ↥V) = v := by
    apply Subtype.ext
    simp [hγ]
  rw [h2, hv] at h1
  exact (congrArg Multiplicative.toAdd h1).symm

omit [Finite W] h in
theorem mem_commSub_range {q : MulAut W} (hq2 : q ^ 2 = 1) {u : W}
    (hu : u ∈ commSub V (Subgroup.zpowers q)) : ∃ v ∈ V, u = q v * v⁻¹ := by
  let φ : ↥V →* W :=
    { toFun := fun v => q (v : W) * (v : W)⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        rw [mul_comm ((y : W)⁻¹) ((x : W)⁻¹)]
        exact mul_mul_mul_comm _ _ _ _ }
  have hle : commSub V (Subgroup.zpowers q) ≤ φ.range := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rcases zpow_sq_eq hq2 k with hk | hk
    · rw [hk]
      exact ⟨1, by simp⟩
    · rw [hk]
      exact ⟨⟨w, hw⟩, rfl⟩
  obtain ⟨v, hv⟩ := hle hu
  exact ⟨v, v.2, hv.symm⟩

theorem same_cim (D : L3Data L V (V ⊓ fixV L)) {p q : MulAut W} (hp : p ∈ L) (hq : q ∈ L)
    (hp1 : p ≠ 1) (hq1 : q ≠ 1) (hp2 : p ^ 2 = 1) (hq2 : q ^ 2 = 1)
    (hquad : ∀ v ∈ V, q (p v * v⁻¹) = p v * v⁻¹) (γp γq : L3.Γ)
    (hγp : D.π γp = ⟨p, hp⟩) (hγq : D.π γq = ⟨q, hq⟩) : L3.cim γp = L3.cim γq := by
  obtain ⟨hcp, hcp'⟩ := commSub_card h hp hp1 hp2
  obtain ⟨hcq, hcq'⟩ := commSub_card h hq hq1 hq2
  have hle : commSub V (Subgroup.zpowers p) ≤ commSub V (Subgroup.zpowers q) := by
    rw [hcq']
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rcases zpow_sq_eq hp2 k with hk | hk
    · rw [hk]
      simp only [MulAut.one_apply, mul_inv_cancel]
      exact one_mem _
    · rw [hk]
      have hpw : p w ∈ V := h.hinv p hp w hw
      have hu : p w * w⁻¹ ∈ V := V.mul_mem hpw (V.inv_mem hw)
      refine ⟨hu, ?_⟩
      intro y hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rcases zpow_sq_eq hq2 j with hj | hj
      · rw [hj]; rfl
      · rw [hj]; exact hquad w hw
  have heq : commSub V (Subgroup.zpowers p) = commSub V (Subgroup.zpowers q) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcp, hcq])
  have key : ∀ (r : MulAut W) (hr : r ∈ L) (γ : L3.Γ) (hγ : D.π γ = ⟨r, hr⟩) (v : ↥V),
      D.β ⟨r (v : W) * (v : W)⁻¹, V.mul_mem (h.hinv r hr v v.2) (V.inv_mem v.2)⟩ =
        Multiplicative.ofAdd (L3.act γ (Multiplicative.toAdd (D.β v)) -
          Multiplicative.toAdd (D.β v)) := by
    intro r hr γ hγ v
    have hrv : r (v : W) ∈ V := h.hinv r hr v v.2
    have h1 := D.equi γ v (by rw [hγ]; exact hrv)
    have h2 : (⟨((D.π γ : ↥L) : MulAut W) (v : W), by rw [hγ]; exact hrv⟩ : ↥V) =
        ⟨r (v : W), hrv⟩ := by
      apply Subtype.ext
      simp [hγ]
    rw [h2] at h1
    have h3 : (⟨r (v : W) * (v : W)⁻¹, V.mul_mem hrv (V.inv_mem v.2)⟩ : ↥V) =
        ⟨r (v : W), hrv⟩ * v⁻¹ := rfl
    rw [h3, map_mul, map_inv, h1, ofAdd_sub, div_eq_mul_inv, ofAdd_toAdd]
    rfl
  have hsub : ∀ (r : MulAut W) (hr : r ∈ L) (γ : L3.Γ) (hγ : D.π γ = ⟨r, hr⟩) (r' : MulAut W)
      (hr' : r' ∈ L) (γ' : L3.Γ) (hγ' : D.π γ' = ⟨r', hr'⟩) (hr2 : r ^ 2 = 1) (hr2' : r' ^ 2 = 1)
      (hrr : commSub V (Subgroup.zpowers r) ≤ commSub V (Subgroup.zpowers r')),
      L3.cim γ ⊆ L3.cim γ' := by
    intro r hr γ hγ r' hr' γ' hγ' hr2 hr2' hrr z hz
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨v, hv⟩ := D.β_surj (Multiplicative.ofAdd w)
    have h1 := key r hr γ hγ v
    rw [hv] at h1
    have hvmem : r (v : W) * (v : W)⁻¹ ∈ commSub V (Subgroup.zpowers r) :=
      Subgroup.subset_closure ⟨r, Subgroup.mem_zpowers r, v, v.2, rfl⟩
    obtain ⟨v', hv', hv'eq⟩ := mem_commSub_range hr2' (hrr hvmem)
    have h2 := key r' hr' γ' hγ' ⟨v', hv'⟩
    have h3 : (⟨r (v : W) * (v : W)⁻¹, V.mul_mem (h.hinv r hr v v.2) (V.inv_mem v.2)⟩ : ↥V) =
        ⟨r' v' * v'⁻¹, V.mul_mem (h.hinv r' hr' v' hv') (V.inv_mem hv')⟩ :=
      Subtype.ext (by simpa using hv'eq)
    rw [h3, h2] at h1
    refine Finset.mem_image.2 ⟨Multiplicative.toAdd (D.β ⟨v', hv'⟩), Finset.mem_univ _, ?_⟩
    have := congrArg Multiplicative.toAdd h1
    simpa using this
  exact Finset.Subset.antisymm (hsub p hp γp hγp q hq γq hγq hp2 hq2 hle)
    (hsub q hq γq hγq p hp γp hγp hq2 hp2 heq.ge)

theorem stab_pair_contra {x y : MulAut W} (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) (hxV : V.map x.toMonoidHom = V) (hyV : V.map y.toMonoidHom = V) : False := by
  have hxL := stab_mem_L h hx hxV
  have hyL := stab_mem_L h hy hyV
  have hx2 := h.hAelem.2 x hx
  have hy2 := h.hAelem.2 y hy
  obtain ⟨D⟩ := h.hnat.toL3Coord
  let e : L3.Γ ≃* ↥L := MulEquiv.ofBijective D.π ⟨pi_injective D, D.π_surj⟩
  have heπ : ∀ γ, (e γ) = D.π γ := fun γ => rfl
  have hl₁L : σ⁻¹ * x * σ ∈ L := (sigma_conj_mem h x).2 hxL
  have hl₂L : σ⁻¹ * y * σ ∈ L := (sigma_conj_mem h y).2 hyL
  have hconj1 : ∀ z : MulAut W, z ≠ 1 → σ⁻¹ * z * σ ≠ 1 := by
    intro z hz h1
    apply hz
    have h2 : σ * (σ⁻¹ * z * σ) * σ⁻¹ = z := by group
    rw [h1] at h2
    simpa using h2.symm
  have hconj2 : ∀ z : MulAut W, z ^ 2 = 1 → (σ⁻¹ * z * σ) ^ 2 = 1 := by
    intro z hz
    have : (σ⁻¹ * z * σ) ^ 2 = σ⁻¹ * z ^ 2 * σ := by rw [pow_two, pow_two]; group
    rw [this, hz]
    group
  have hxyc : x * y = y * x := h.hAelem.1 x hx y hy
  have hq1 : ∀ v ∈ V, y (x v * v⁻¹) = x v * v⁻¹ := fun v _ => h.hAquad x hx y hy v
  have hq2 : ∀ v ∈ V, (σ⁻¹ * y * σ) ((σ⁻¹ * x * σ) v * v⁻¹) = (σ⁻¹ * x * σ) v * v⁻¹ := by
    intro v hv
    have h1 := h.hAquad x hx y hy (σ v)
    have e1 : x (σ v) = σ ((σ⁻¹ * x * σ) v) := by simp [MulAut.mul_apply]
    have e2 : ∀ u, y (σ u) = σ ((σ⁻¹ * y * σ) u) := fun u => by simp [MulAut.mul_apply]
    rw [e1, ← map_inv, ← map_mul, e2] at h1
    exact σ.injective h1
  have hγx : D.π (e.symm ⟨x, hxL⟩) = ⟨x, hxL⟩ := e.apply_symm_apply _
  have hγy : D.π (e.symm ⟨y, hyL⟩) = ⟨y, hyL⟩ := e.apply_symm_apply _
  have hγ₁ : D.π (e.symm ⟨σ⁻¹ * x * σ, hl₁L⟩) = ⟨σ⁻¹ * x * σ, hl₁L⟩ := e.apply_symm_apply _
  have hγ₂ : D.π (e.symm ⟨σ⁻¹ * y * σ, hl₂L⟩) = ⟨σ⁻¹ * y * σ, hl₂L⟩ := e.apply_symm_apply _
  have hsame := same_cim h D hxL hyL hx1 hy1 hx2 hy2 hq1 _ _ hγx hγy
  have hsame' := same_cim h D hl₁L hl₂L (hconj1 x hx1) (hconj1 y hy1) (hconj2 x hx2)
    (hconj2 y hy2) hq2 _ _ hγ₁ hγ₂
  let ϑ : ↥L ≃* ↥L :=
    { toFun := fun l => ⟨σ⁻¹ * (l : MulAut W) * σ, (sigma_conj_mem h _).2 l.2⟩
      invFun := fun l => ⟨σ * (l : MulAut W) * σ⁻¹, (h.hσL _).1 l.2⟩
      left_inv := fun l => by apply Subtype.ext; simp [mul_assoc]
      right_inv := fun l => by apply Subtype.ext; simp [mul_assoc]
      map_mul' := fun a b => by apply Subtype.ext; simp [mul_assoc] }
  let θ : L3.Γ ≃* L3.Γ := (e.trans ϑ).trans e.symm
  have hθx : θ (e.symm ⟨x, hxL⟩) = e.symm ⟨σ⁻¹ * x * σ, hl₁L⟩ := by
    simp [θ, ϑ]
  have hθy : θ (e.symm ⟨y, hyL⟩) = e.symm ⟨σ⁻¹ * y * σ, hl₂L⟩ := by
    simp [θ, ϑ]
  have hθ : ¬ ∃ g : L3.Γ, ∀ z : L3.Γ, θ z = g * z * g⁻¹ := by
    rintro ⟨g, hg⟩
    apply h.hdyn
    refine ⟨((e g : ↥L) : MulAut W)⁻¹, L.inv_mem (e g).2, ?_⟩
    intro z hz
    have h1 := congrArg (fun γ => ((e γ : ↥L) : MulAut W)) (hg (e.symm ⟨z, hz⟩))
    simp only [θ, ϑ, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, map_mul] at h1
    have h2 : σ⁻¹ * z * σ = ((e g : ↥L) : MulAut W) * z * ((e g : ↥L) : MulAut W)⁻¹ := by
      simpa using h1
    calc (σ * ((e g : ↥L) : MulAut W)⁻¹⁻¹) * z
        = σ * (((e g : ↥L) : MulAut W) * z * ((e g : ↥L) : MulAut W)⁻¹) *
            ((e g : ↥L) : MulAut W) := by group
      _ = σ * (σ⁻¹ * z * σ) * ((e g : ↥L) : MulAut W) := by rw [h2]
      _ = z * (σ * ((e g : ↥L) : MulAut W)⁻¹⁻¹) := by group
  have hsw := outer_swaps_same_center θ hθ (isInvol_of e hxL hx1 hx2) (isInvol_of e hyL hy1 hy2)
    (fun h1 => hxy (by
      have := congrArg (fun γ => ((e γ : ↥L) : MulAut W)) h1
      simpa using this))
    (by
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      simpa using hxyc) hsame
  apply hsw
  rw [hθx, hθy]
  exact hsame'

theorem core : False := by
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply h.hAne
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (hcon x hx)
  by_cases hall : ∃ b ∈ A, b ≠ 1 ∧ b ≠ a
  · obtain ⟨b, hbA, hb1, hba⟩ := hall
    by_cases hxV : V.map a.toMonoidHom = V
    · by_cases hyV : V.map b.toMonoidHom = V
      · exact stab_pair_contra h haA hbA (Ne.symm hba) ha1 hb1 hxV hyV
      · exact pair_contra h hbA hyV haA ha1 hxV
    · by_cases hyV : V.map b.toMonoidHom = V
      · exact pair_contra h haA hxV hbA hb1 hyV
      · have hab : a * b ∈ A := A.mul_mem haA hbA
        have ha2 : a ^ 2 = 1 := h.hAelem.2 a haA
        have hab1 : a * b ≠ 1 := by
          intro h1
          apply hba
          have h2 : b = a⁻¹ := by
            have := congrArg (fun z => a⁻¹ * z) h1
            simpa using this
          rw [h2]
          exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ha2)
        have haσ : V.map a.toMonoidHom = V.map σ.toMonoidHom :=
          (perm h (h.hAN a haA)).resolve_left hxV
        have hbσ : V.map b.toMonoidHom = V.map σ.toMonoidHom :=
          (perm h (h.hAN b hbA)).resolve_left hyV
        have hstab : V.map (a * b).toMonoidHom = V := by
          rw [map_mul_aut, hbσ, ← haσ, ← map_mul_aut, ← pow_two, ha2, map_one_aut]
        exact pair_contra h haA hxV hab hab1 hstab
  · push Not at hall
    exact rank_contra h haA ha1 (fun b hb => by
      by_cases hb1 : b = 1
      · exact Or.inl hb1
      · exact Or.inr (hall b hb hb1))

end N4Core

theorem n4Stmt_of : N4Stmt := by
  intro W _ _ M Mp T L A V σ hstd hMp hA hσT hσM hσN hdyn hσV hsum hPSL hnat
  by_contra hZne
  exact N4Core.core (N4Cfg.of_hyps hstd hMp hA hσN hdyn hσV hsum hPSL hnat hZne)

end CFSG.Quasithin
