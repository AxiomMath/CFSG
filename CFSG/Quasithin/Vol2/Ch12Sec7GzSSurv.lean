module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzSFr
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSW
public import CFSG.Quasithin.Vol2.Ch12Sec7IdentA
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open Certificates.Data.S1277Struct Certificates.Data.S1277Cand
  Certificates.Data.S1277Sig Certificates.Data.S1277Surv Certificates.Data.S1277Bfs Std Subgroup
open scoped commutatorElement

theorem two_elem_list (l : List Nat) (hnd : l.Nodup) (hlen : l.length = 2) {a b : Nat}
    (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) : ∀ p ∈ l, p = a ∨ p = b := by
  rcases List.length_eq_two.1 hlen with ⟨x, y, rfl⟩
  intro p hp
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha hb hp
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hp with rfl | rfl <;> simp_all

section Extra

variable {G : Type} [Group G] [Finite G] {H K Q : Subgroup G} {T : KTab} {κ : G → Nat}

theorem surv_phi (S : KSetting H K Q T κ) {z : G} (hzK : z ∈ K) {zN : Nat} (hκz : κ z = zN)
    {N : List Nat} (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ n ∈ N) (hpl : plOK T (phiList T N) = true)
    (hPl2 : (phiList T N).length = 2) (hzPl : zN ∈ phiList T N) (hzne : zN ≠ oneN T) :
    z ∈ Phi' Q ∧ ∀ r ∈ Phi' Q, r = 1 ∨ r = z := by
  have hPlset : ∀ p ∈ phiList T N, p = oneN T ∨ p = zN :=
    two_elem_list _ (phiList_nodup T N) hPl2 (one_mem_phiList T N) hzPl (Ne.symm hzne)
  refine ⟨?_, fun r hr => ?_⟩
  · obtain ⟨r, hr, hrz⟩ := (mem_phiList_iff S hQN hpl zN).1 hzPl
    have : r = z := S.hκ.inj r (S.hQK (Phi'_le Q hr)) z hzK (hrz.trans hκz.symm)
    rw [← this]; exact hr
  · have hrN : κ r ∈ phiList T N := (mem_phiList_iff S hQN hpl _).2 ⟨r, hr, rfl⟩
    have hrK : r ∈ K := S.hQK (Phi'_le Q hr)
    rcases hPlset _ hrN with h | h
    · left
      exact S.hκ.inj r hrK 1 K.one_mem (h.trans S.hκ.one.symm)
    · right
      exact S.hκ.inj r hrK z hzK (h.trans hκz.symm)

theorem surv_extraspecial (S : KSetting H K Q T κ) {z : G} (hzK : z ∈ K)
    (hzH : ∀ h ∈ H, h * z = z * h) {zN : Nat} (hκz : κ z = zN) {N : List Nat}
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ n ∈ N) (hpl : plOK T (phiList T N) = true)
    (D : FrData H Q (Phi' Q) 6) (hPl2 : (phiList T N).length = 2) (hzPl : zN ∈ phiList T N)
    (hzne : zN ≠ oneN T) (hzsq : mulN T zN zN = oneN T)
    (hE : eCheck T N (phiList T N) zN = true) : IsExtraspecialPGroup 2 ↥Q := by
  classical
  obtain ⟨hzΦ, hΦeq⟩ := surv_phi S hzK hκz hQN hpl hPl2 hzPl hzne
  have hzQ : z ∈ Q := Phi'_le Q hzΦ
  have hzz : z * z = 1 := by
    apply S.hκ.inj _ (K.mul_mem hzK hzK) 1 K.one_mem
    rw [S.hκ.mul z hzK z hzK, hκz, hzsq, S.hκ.one]
  have hz1 : z ≠ 1 := by
    intro h
    apply hzne
    rw [← hκz, h, S.hκ.one]
  let zQ : ↥Q := ⟨z, hzQ⟩
  have hzQsq : zQ * zQ = 1 := Subtype.ext hzz
  have hzQ1 : zQ ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hmemZ : ∀ y : ↥Q, y ∈ Subgroup.zpowers zQ ↔ (y : G) = 1 ∨ (y : G) = z := by
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      have hk : ∀ k : ℤ, zQ ^ k = 1 ∨ zQ ^ k = zQ := by
        intro k
        have hsq : zQ ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hzQsq
        have : zQ ^ k = zQ ^ (k % 2) := by
          conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
          rw [zpow_add, zpow_mul, hsq, one_zpow, mul_one]
        rw [this]
        have h2 : k % 2 = 0 ∨ k % 2 = 1 := by omega
        rcases h2 with h | h <;> rw [h] <;> simp
      rcases hk k with h | h
      · left; exact congrArg Subtype.val h
      · right; exact congrArg Subtype.val h
    · rintro (h | h)
      · have : y = 1 := Subtype.ext h
        rw [this]; exact Subgroup.one_mem _
      · have : y = zQ := Subtype.ext h
        rw [this]; exact Subgroup.mem_zpowers _
  have hΦz : ∀ y : ↥Q, (y : G) ∈ Phi' Q → y ∈ Subgroup.zpowers zQ := fun y hy =>
    (hmemZ y).2 (hΦeq _ hy)
  have hcenter : Subgroup.center ↥Q = Subgroup.zpowers zQ := by
    apply _root_.le_antisymm
    · intro x hx
      rw [Subgroup.mem_center_iff] at hx
      have hxN : κ x.1 ∈ phiList T N := by
        have hxκ : κ x.1 ∈ N := (hQN _).1 ⟨x.1, x.2, rfl⟩
        unfold eCheck at hE
        simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
          Bool.not_eq_true', beq_iff_eq, List.contains_iff_mem] at hE
        have := hE.1 (κ x.1) hxκ
        rcases this with h | h
        · exfalso
          have hall : ∀ n ∈ N, mulN T (κ x.1) n = mulN T n (κ x.1) := by
            intro n hn
            obtain ⟨y, hy, rfl⟩ := (hQN n).2 hn
            rw [← S.hκ.mul x.1 (S.hQK x.2) y (S.hQK hy), ← S.hκ.mul y (S.hQK hy) x.1 (S.hQK x.2)]
            congr 1
            exact (congrArg Subtype.val (hx ⟨y, hy⟩)).symm
          have : (N.all fun y => mulN T (κ x.1) y == mulN T y (κ x.1)) = true :=
            List.all_eq_true.2 fun n hn => beq_iff_eq.2 (hall n hn)
          rw [this] at h
          exact absurd h (by simp)
        · exact h
      have := (mem_phiList_iff S hQN hpl _).1 hxN
      obtain ⟨r, hr, hrx⟩ := this
      have hrx' : r = x.1 := S.hκ.inj r (S.hQK (Phi'_le Q hr)) x.1 (S.hQK x.2) hrx
      exact hΦz x (hrx' ▸ hr)
    · rw [Subgroup.zpowers_le]
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hzH g.1 (S.hKH (S.hQK g.2)))
  have hcomm : commutator ↥Q = Subgroup.zpowers zQ := by
    apply _root_.le_antisymm
    · rw [_root_.commutator_def]
      refine Subgroup.commutator_le.2 ?_
      intro a _ b _
      apply hΦz
      have := comm_mem_Phi' a.2 b.2
      simpa [commutatorElement_def] using this
    · rw [Subgroup.zpowers_le]
      unfold eCheck at hE
      simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at hE
      obtain ⟨x, hx, y, hy, hxy⟩ := hE.2
      obtain ⟨a, ha, rfl⟩ := (hQN x).2 hx
      obtain ⟨b, hb, rfl⟩ := (hQN y).2 hy
      have : a * b * a⁻¹ * b⁻¹ = z := by
        apply S.hκ.inj _ (K.mul_mem (K.mul_mem (K.mul_mem (S.hQK ha) (S.hQK hb))
          (K.inv_mem (S.hQK ha))) (K.inv_mem (S.hQK hb))) z hzK
        rw [S.hκ.comm S.hinv (S.hQK ha) (S.hQK hb), hxy, hκz]
      have hz' : (⁅(⟨a, ha⟩ : ↥Q), ⟨b, hb⟩⁆ : ↥Q) = zQ := Subtype.ext (by
        simpa [commutatorElement_def] using this)
      rw [← hz', _root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hfratt : frattini ↥Q = Subgroup.zpowers zQ := by
    apply _root_.le_antisymm
    · intro x hx
      exact hΦz x (D.frattini_le hx)
    · rw [Subgroup.zpowers_le]
      exact Phi'_frattini S.hQ2 z hzΦ
  have hcard : Nat.card (Subgroup.center ↥Q) = 2 := by
    rw [hcenter, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hzQsq) hzQ1
  exact ⟨S.hQ2, hcomm.trans hcenter.symm, hfratt.trans hcenter.symm, hcard⟩

end Extra

section Unpack

theorem survCheck_spec {T : KTab} {N : List Nat} {zN : Nat} {Pl : List Nat} {d typ : Nat}
    {tab : HashMap Nat Nat} {sl : List (List Nat)}
    (h : survCheck T N zN Pl d typ tab sl = true) :
    ∃ (cap : Nat) (sigP gensK sg : List Nat) (S0 : Node) (nodes : List Node),
      cap = (klist T).length / N.length * 105 ∧ sigP = sl.map packC ∧
      gensK = survGensK T N Pl d tab ∧ sg = shortGens cap gensK ∧
      S0 = ⟨sg, sortSet (closW sg (cap + 1))⟩ ∧
      nodes = survNodes cap sigP S0 3 ∧ d = 6 ∧ typ = 1 ∧ plOK T Pl = true ∧
      frOK T N Pl d tab = true ∧ phiOK T zN Pl N typ d tab = true ∧ Pl.length = 2 ∧ zN ∈ Pl ∧
      zN ≠ oneN T ∧ mulN T zN zN = oneN T ∧
      N.length * ((klist T).length / N.length) = (klist T).length ∧
      sl.length % ((klist T).length / N.length) = 0 ∧
      (∃ j, j < 20 ∧ sl.length / ((klist T).length / N.length) = 105 * 2 ^ j) ∧
      kgensOK T = true ∧ repOK T N Pl d tab = true ∧
      S0.elems.length = (klist T).length / N.length ∧ latOK cap sigP nodes S0 = true ∧
      eCheck T N Pl zN = true ∧
      ∀ S ∈ nodes, S.elems = S0.elems ∨ (S.elems.length / ((klist T).length / N.length)) % 2 = 0 ∨
        vlOK T N tab S = true := by
  refine ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  unfold survCheck at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq,
    List.contains_iff_mem, List.any_eq_true, List.mem_range, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hd, htyp⟩, hpl⟩, hfr⟩, hphi⟩, hl2⟩, hzmem⟩, hzne⟩, hzsq⟩, hnek⟩, hmod⟩,
    hj⟩, hkg⟩, hrep⟩, hS0⟩, hlat⟩, hE⟩, hnodes⟩ := h
  refine ⟨hd, htyp, hpl, hfr, hphi, hl2, hzmem, hzne, hzsq, hnek, hmod, hj, hkg, hrep, hS0, hlat,
    hE, fun S hS => ?_⟩
  rcases (hnodes S hS) with (h1 | h1) | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

theorem kgensOK_spec {T : KTab} (h : kgensOK T = true) : ∀ g ∈ kgensOf T, g < T.nb * 64 := by
  unfold kgensOK at h
  simpa [List.all_eq_true] using h

theorem repOK_spec {T : KTab} {N Pl : List Nat} {d : Nat} {tab : HashMap Nat Nat}
    (h : repOK T N Pl d tab = true) : ∀ i < d, repOf T (basisOf T N Pl) (2 ^ i) ∈ N ∧
      tab.getD (repOf T (basisOf T N Pl) (2 ^ i)) 0 = 2 ^ i := by
  unfold repOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, List.contains_iff_mem,
    beq_iff_eq] at h
  exact h

end Unpack

section Hom

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G}

theorem card_range_eq_of_pkSet {φ : Nat → Nat} {R : Subgroup (Equiv.Perm (Fin (2 ^ 6)))}
    (hR : R ≤ Sig 6 φ) {S : List Nat} (hnd : S.Nodup) (hS : ∀ y, pkSet R y ↔ y ∈ S) :
    Nat.card R = S.length := by
  classical
  let f : ↥R → {y : Nat // y ∈ S} := fun r => ⟨pk r.1, (hS _).1 ⟨r.1, r.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact Subtype.ext (pk_injective (hR a.2) (hR b.2) (congrArg Subtype.val hab))
    · rintro ⟨y, hy⟩
      obtain ⟨r, hr, rfl⟩ := (hS y).2 hy
      exact ⟨⟨r, hr⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf)]
  have e2 : {y : Nat // y ∈ S} ≃ ↥S.toFinset := Equiv.subtypeEquivRight fun c => by simp
  rw [Nat.card_congr e2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup hnd]

theorem exists_sl_hom (D : FrData H Q (Phi' Q) 6) {φ : Nat → Nat} (hR : D.rho.range ≤ Sig 6 φ)
    (hQmax : ∀ X : Subgroup G, X ≤ H → (∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) → IsPGroup 2 ↥X →
      X ≤ Q)
    (hQ2 : IsPGroup 2 ↥Q) (hC : ∀ h ∈ H, (∀ x ∈ Q, h * x = x * h) → h ∈ Q)
    {S : Node} (hnd : S.elems.Nodup) (hS : ∀ y, pkSet D.rho.range y ↔ y ∈ S.elems)
    (u : List Nat) (hlen : S.elems.length = 168)
    (hmul : ∀ a ∈ S.elems, ∀ b ∈ S.elems, restr u (mulS a b) = restr u a * restr u b)
    (hdet : ∀ a ∈ S.elems, (restr u a).det = 1)
    (hid : ∀ a ∈ S.elems, restr u a = 1 → a = oneS) :
    ∃ f : ↥H →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      Function.Surjective f ∧ f.ker = Q.subgroupOf H := by
  classical
  have hNfr := Phi'_frattini hQ2
  have hpkS : ∀ h : ↥H, pk (D.rho h) ∈ S.elems := fun h => (hS _).1 ⟨D.rho h, ⟨h, rfl⟩, rfl⟩
  let F : ↥H → Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    fun h => ⟨restr u (pk (D.rho h)), hdet _ (hpkS h)⟩
  have hF : ∀ h h', F (h * h') = F h * F h' := by
    intro h h'
    apply Subtype.ext
    show restr u (pk (D.rho (h * h'))) = restr u (pk (D.rho h)) * restr u (pk (D.rho h'))
    rw [map_mul, pk_mul (hR ⟨h, rfl⟩).1, hmul _ (hpkS h) _ (hpkS h')]
  let f : ↥H →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := MonoidHom.mk' F hF
  have hfval : ∀ h, f h = F h := fun h => rfl
  have hker : f.ker = Q.subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h2 : restr u (pk (D.rho h)) = 1 := by
        have := congrArg Subtype.val h1
        rw [hfval] at this
        simpa [F] using this
      have h3 : pk (D.rho h) = pk 1 := by rw [pk_one]; exact hid _ (hpkS h) h2
      have h4 : D.rho h = 1 := pk_injective (hR ⟨h, rfl⟩) (Sig 6 φ).one_mem h3
      exact D.mem_of_rho_eq_one hQmax hQ2 hC hNfr h4
    · intro h1
      have h2 : D.rho h = 1 := D.rho_eq_one_of_mem h1
      have : F h = F 1 := Subtype.ext (by
        show restr u (pk (D.rho h)) = restr u (pk (D.rho 1))
        rw [h2, map_one])
      rw [hfval, this, ← hfval, f.map_one]
  refine ⟨f, ?_, hker⟩
  have h1 : Nat.card f.ker * Nat.card f.range = Nat.card H := Subgroup.card_ker_mul_card_range f
  rw [hker] at h1
  have h2 : Nat.card ↥(Q.subgroupOf H) = Nat.card ↥Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe D.hQH).toEquiv
  rw [h2] at h1
  have h3 : Nat.card H = Nat.card Q * Nat.card D.rho.range := D.card_H hQmax hQ2 hC hNfr
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have h4 : Nat.card f.range = Nat.card D.rho.range := by
    have : Nat.card Q * Nat.card f.range = Nat.card Q * Nat.card D.rho.range := by
      rw [h1, h3]
    exact Nat.eq_of_mul_eq_mul_left hQpos this
  have h5 : Nat.card D.rho.range = 168 := by
    rw [card_range_eq_of_pkSet hR hnd hS, hlen]
  have h6 : f.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [h4, h5, card_sl32]
  exact MonoidHom.range_eq_top.1 h6

end Hom

section AB

variable {G : Type} [Group G] [Finite G] {H K Q : Subgroup G} {T : KTab} {κ : G → Nat}

theorem vlCheck_spec {T : KTab} {N : List Nat} {tab : HashMap Nat Nat} {S : Node}
    {N1 N2 : List Nat} (h : vlCheck T N tab S N1 N2 = true) :
    S.elems.length = 168 ∧ 0 ∈ N1 ∧ 0 ∈ N2 ∧ (∀ a ∈ N1, a < 64) ∧ (∀ a ∈ N2, a < 64) ∧
      (∀ a ∈ N1, ∀ b ∈ N1, a ^^^ b ∈ N1) ∧ (∀ a ∈ N2, ∀ b ∈ N2, a ^^^ b ∈ N2) ∧
      (∀ a ∈ N1, a ∈ N2 → a = 0) ∧ (∀ c < 64, ∃ a ∈ N1, ∃ b ∈ N2, a ^^^ b = c) ∧
      (∀ s ∈ S.elems, (∀ a ∈ N1, applyCols (unpackC 6 s) a ∈ N1) ∧
        ∀ a ∈ N2, applyCols (unpackC 6 s) a ∈ N2) ∧
      (N.filter fun x => N1.contains (tab.getD x 0)).length = 16 ∧
      (N.filter fun x => N2.contains (tab.getD x 0)).length = 16 ∧
      (∀ x ∈ N.filter (fun x => N1.contains (tab.getD x 0)),
        ∀ y ∈ N.filter (fun x => N1.contains (tab.getD x 0)), mulN T x y = mulN T y x) ∧
      (∀ x ∈ N.filter (fun x => N1.contains (tab.getD x 0)), mulN T x x = oneN T) ∧
      (∀ x ∈ N.filter (fun x => N2.contains (tab.getD x 0)),
        ∀ y ∈ N.filter (fun x => N2.contains (tab.getD x 0)), mulN T x y = mulN T y x) ∧
      (∀ x ∈ N.filter (fun x => N2.contains (tab.getD x 0)), mulN T x x = oneN T) ∧
      (∀ a ∈ S.elems, ∀ b ∈ S.elems,
        restr (basis3 N1) (mulS a b) = restr (basis3 N1) a * restr (basis3 N1) b) ∧
      (∀ a ∈ S.elems, (restr (basis3 N1) a).det = 1) ∧
      (∀ a ∈ S.elems, restr (basis3 N1) a = 1 → a = oneS) := by
  unfold vlCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, List.all_eq_true,
    List.any_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, List.mem_range,
    and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  refine ⟨h1, h2, h3, fun a ha => h4 a ha, fun a ha => h5 a ha, fun a ha b hb => h6 a ha b hb,
    fun a ha b hb => h7 a ha b hb, ?_, fun c hc => h9 c hc, fun s hs => h10 s hs, h11, h12,
    fun x hx y hy => h13 x hx y hy, fun x hx => h14 x hx, fun x hx y hy => h15 x hx y hy,
    fun x hx => h16 x hx, fun a ha b hb => h17 a ha b hb, fun a ha => h18 a ha,
    fun a ha => h19 a ha⟩
  intro a ha ha2
  rcases h8 a ha with h | h
  · exact h
  · exact absurd ha2 (by simpa using h)

theorem exists_sub (S : KSetting H K Q T κ) {N : List Nat} (hNnd : N.Nodup)
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ n ∈ N) {d : Nat} (D : FrData H Q (Phi' Q) d)
    {tab : HashMap Nat Nat} (hD : ∀ x, D.wc x = tab.getD (κ x) 0) {N1 : List Nat} (h0 : 0 ∈ N1)
    (hxor : ∀ a ∈ N1, ∀ b ∈ N1, a ^^^ b ∈ N1)
    (hcard : (N.filter fun x => N1.contains (tab.getD x 0)).length = 16)
    (hcomm : ∀ x ∈ N.filter (fun x => N1.contains (tab.getD x 0)),
      ∀ y ∈ N.filter (fun x => N1.contains (tab.getD x 0)), mulN T x y = mulN T y x)
    (hsq : ∀ x ∈ N.filter (fun x => N1.contains (tab.getD x 0)), mulN T x x = oneN T)
    (hH : ∀ h ∈ H, ∀ x ∈ Q, D.wc x ∈ N1 → D.wc (h * x * h⁻¹) ∈ N1) :
    ∃ A : Subgroup G, (∀ x, x ∈ A ↔ x ∈ Q ∧ D.wc x ∈ N1) ∧ IsElemAbelian 2 A ∧
      Nat.card A = 16 ∧ H ≤ Subgroup.normalizer (A : Set G) := by
  classical
  let A : Subgroup G :=
    { carrier := {x | x ∈ Q ∧ D.wc x ∈ N1}
      one_mem' := ⟨Q.one_mem, by rw [D.wc_one]; exact h0⟩
      mul_mem' := fun {a b} ha hb => ⟨Q.mul_mem ha.1 hb.1, by
        rw [D.wc_mul _ ha.1 _ hb.1]; exact hxor _ ha.2 _ hb.2⟩
      inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, by rw [D.wc_inv ha.1]; exact ha.2⟩ }
  have hA : ∀ x, x ∈ A ↔ x ∈ Q ∧ D.wc x ∈ N1 := fun x => Iff.rfl
  have hAK : A ≤ K := fun x hx => S.hQK ((hA x).1 hx).1
  have hcodes : ∀ n, (∃ a ∈ A, κ a = n) ↔ n ∈ N.filter (fun x => N1.contains (tab.getD x 0)) := by
    intro n
    rw [List.mem_filter]
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨haQ, haN⟩ := (hA a).1 ha
      refine ⟨(hQN _).1 ⟨a, haQ, rfl⟩, ?_⟩
      rw [← hD a]
      exact List.contains_iff_mem.2 haN
    · rintro ⟨hn, hc⟩
      obtain ⟨q, hq, rfl⟩ := (hQN n).2 hn
      refine ⟨q, (hA q).2 ⟨hq, ?_⟩, rfl⟩
      rw [hD q]
      exact List.contains_iff_mem.1 hc
  refine ⟨A, hA, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_, ?_⟩
  · apply Subtype.ext
    have ha := (hcodes (κ a.1)).1 ⟨a.1, a.2, rfl⟩
    have hb := (hcodes (κ b.1)).1 ⟨b.1, b.2, rfl⟩
    have h1 := hcomm _ ha _ hb
    rw [← S.hκ.mul a.1 (hAK a.2) b.1 (hAK b.2), ← S.hκ.mul b.1 (hAK b.2) a.1 (hAK a.2)] at h1
    exact S.hκ.inj _ (K.mul_mem (hAK a.2) (hAK b.2)) _ (K.mul_mem (hAK b.2) (hAK a.2)) h1
  · have hx' := (hcodes (κ x)).1 ⟨x, hx, rfl⟩
    have h1 := hsq _ hx'
    rw [← S.hκ.mul x (hAK hx) x (hAK hx), ← S.hκ.one] at h1
    have := S.hκ.inj _ (K.mul_mem (hAK hx) (hAK hx)) 1 K.one_mem h1
    rw [pow_two]; exact this
  · rw [card_of_codes S.hκ hAK ((hNnd.filter _)) hcodes, hcard]
  · intro h hh
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ h ∈ H, ∀ x, x ∈ A → h * x * h⁻¹ ∈ A := by
      intro h hh x hx
      obtain ⟨hxQ, hxN⟩ := (hA x).1 hx
      exact (hA _).2 ⟨S.hQn h hh x hxQ, hH h hh x hxQ hxN⟩
    intro x
    constructor
    · exact key h hh x
    · intro hx
      have := key h⁻¹ (H.inv_mem hh) _ hx
      have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
      rwa [e] at this

theorem wc_conj_eq_apply (D : FrData H Q (Phi' Q) 6) {φ : Nat → Nat}
    (hR : D.rho.range ≤ Sig 6 φ) {h : G} (hh : h ∈ H) {x : G} (hx : x ∈ Q) :
    D.wc (h * x * h⁻¹) = applyCols (unpackC 6 (pk (D.rho ⟨h, hh⟩))) (D.wc x) := by
  have h1 := D.rho_of_mem ⟨h, hh⟩ hx
  rw [unpackC_pk]
  have h2 := applyCols_colsOf (hR ⟨⟨h, hh⟩, rfl⟩).1 ⟨D.wc x, D.wc_lt x hx⟩
  rw [← h2]
  exact h1.symm

theorem exists_AB (S : KSetting H K Q T κ) {N : List Nat} (hNnd : N.Nodup)
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ n ∈ N) {D : FrData H Q (Phi' Q) 6}
    {tab : HashMap Nat Nat} (hD : ∀ x, D.wc x = tab.getD (κ x) 0) {z : G} (hzΦ : z ∈ Phi' Q)
    (hΦeq : ∀ r ∈ Phi' Q, r = 1 ∨ r = z) {φ : Nat → Nat} (hR : D.rho.range ≤ Sig 6 φ)
    {Sn : Node} (hS : ∀ y, pkSet D.rho.range y ↔ y ∈ Sn.elems) {N1 N2 : List Nat}
    (hv : vlCheck T N tab Sn N1 N2 = true) :
    ∃ A B : Subgroup G, IsElemAbelian 2 A ∧ IsElemAbelian 2 B ∧ Nat.card A = 16 ∧
      Nat.card B = 16 ∧ A ⊔ B = Q ∧ A ⊓ B = Subgroup.zpowers z ∧
      H ≤ Subgroup.normalizer (A : Set G) ∧ H ≤ Subgroup.normalizer (B : Set G) := by
  classical
  obtain ⟨-, h0₁, h0₂, hlt₁, hlt₂, hxor₁, hxor₂, hinter, hcover, hinv, hc₁, hc₂, hcm₁, hsq₁, hcm₂,
    hsq₂, -, -, -⟩ := vlCheck_spec hv
  have hH₁ : ∀ h ∈ H, ∀ x ∈ Q, D.wc x ∈ N1 → D.wc (h * x * h⁻¹) ∈ N1 := by
    intro h hh x hx hxN
    rw [wc_conj_eq_apply D hR hh hx]
    exact (hinv _ ((hS _).1 ⟨D.rho ⟨h, hh⟩, ⟨⟨h, hh⟩, rfl⟩, rfl⟩)).1 _ hxN
  have hH₂ : ∀ h ∈ H, ∀ x ∈ Q, D.wc x ∈ N2 → D.wc (h * x * h⁻¹) ∈ N2 := by
    intro h hh x hx hxN
    rw [wc_conj_eq_apply D hR hh hx]
    exact (hinv _ ((hS _).1 ⟨D.rho ⟨h, hh⟩, ⟨⟨h, hh⟩, rfl⟩, rfl⟩)).2 _ hxN
  obtain ⟨A, hA, hAab, hAc, hAn⟩ := exists_sub S hNnd hQN D hD h0₁ hxor₁ hc₁ hcm₁ hsq₁ hH₁
  obtain ⟨B, hB, hBab, hBc, hBn⟩ := exists_sub S hNnd hQN D hD h0₂ hxor₂ hc₂ hcm₂ hsq₂ hH₂
  refine ⟨A, B, hAab, hBab, hAc, hBc, ?_, ?_, hAn, hBn⟩
  · apply _root_.le_antisymm
    · exact sup_le (fun x hx => ((hA x).1 hx).1) (fun x hx => ((hB x).1 hx).1)
    · intro x hx
      have hxlt : D.wc x < 2 ^ 6 := D.wc_lt x hx
      obtain ⟨a₁, ha₁, b₁, hb₁, hab⟩ := hcover (D.wc x) (by simpa using hxlt)
      obtain ⟨xa, hxaQ, hxa⟩ := D.wc_surj a₁ (by have := hlt₁ a₁ ha₁; omega)
      obtain ⟨xb, hxbQ, hxb⟩ := D.wc_surj b₁ (by have := hlt₂ b₁ hb₁; omega)
      have hxaA : xa ∈ A := (hA xa).2 ⟨hxaQ, by rw [hxa]; exact ha₁⟩
      have hxbB : xb ∈ B := (hB xb).2 ⟨hxbQ, by rw [hxb]; exact hb₁⟩
      have hy : x * (xa * xb)⁻¹ ∈ Phi' Q := by
        rw [← D.wc_ker _ (Q.mul_mem hx (Q.inv_mem (Q.mul_mem hxaQ hxbQ))),
          D.wc_mul _ hx _ (Q.inv_mem (Q.mul_mem hxaQ hxbQ)), D.wc_inv (Q.mul_mem hxaQ hxbQ),
          D.wc_mul _ hxaQ _ hxbQ, hxa, hxb, hab, Nat.xor_self]
      have hzA : z ∈ A := (hA z).2 ⟨Phi'_le Q hzΦ, by
        rw [(D.wc_ker z (Phi'_le Q hzΦ)).2 hzΦ]; exact h0₁⟩
      have hyA : x * (xa * xb)⁻¹ ∈ A := by
        rcases hΦeq _ hy with h | h
        · rw [h]; exact A.one_mem
        · rw [h]; exact hzA
      have hmem : x * (xa * xb)⁻¹ * xa * xb ∈ A ⊔ B :=
        (A ⊔ B).mul_mem ((le_sup_left : A ≤ A ⊔ B) (A.mul_mem hyA hxaA))
          ((le_sup_right : B ≤ A ⊔ B) hxbB)
      have e : x * (xa * xb)⁻¹ * xa * xb = x := by group
      rwa [e] at hmem
  · apply _root_.le_antisymm
    · intro x hx
      obtain ⟨hxQ, hxN1⟩ := (hA x).1 hx.1
      obtain ⟨-, hxN2⟩ := (hB x).1 hx.2
      have h0 : D.wc x = 0 := hinter _ hxN1 hxN2
      have hxΦ : x ∈ Phi' Q := (D.wc_ker x hxQ).1 h0
      rcases hΦeq x hxΦ with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers z
    · rw [Subgroup.zpowers_le]
      have hz0 : D.wc z = 0 := (D.wc_ker z (Phi'_le Q hzΦ)).2 hzΦ
      exact ⟨(hA z).2 ⟨Phi'_le Q hzΦ, by rw [hz0]; exact h0₁⟩,
        (hB z).2 ⟨Phi'_le Q hzΦ, by rw [hz0]; exact h0₂⟩⟩

end AB

section Branch

variable {G : Type} [Group G] [Finite G] {H K Q : Subgroup G} {T : KTab} {κ : G → Nat}

theorem survOK_unfold {T : KTab} {N : List Nat} {zN : Nat} (h : survOK T N zN = true) :
    ∃ (Pl : List Nat) (d typ : Nat) (tab : HashMap Nat Nat) (pt : List Nat),
      Pl = phiList T N ∧ pt = phiTab T zN Pl N typ d tab ∧
      survCheck T N zN Pl d typ tab (sigList d (phiFn pt)) = true :=
  ⟨_, _, _, _, _, rfl, rfl, h⟩

theorem latOK_valid {cap : Nat} {sigP : List Nat} {nodes : List Node} {S0 : Node}
    (h : latOK cap sigP nodes S0 = true) : ∀ S ∈ nodes, nodeValidW cap S = true := by
  unfold latOK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  intro S hS
  exact (h.2 S hS).1.1.1

theorem vlOK_spec {T : KTab} {N : List Nat} {tab : HashMap Nat Nat} {S : Node}
    (h : vlOK T N tab S = true) : ∃ N1 N2, vlCheck T N tab S N1 N2 = true := by
  unfold vlOK at h
  cases hf : findPair S.gens with
  | none => rw [hf] at h; simp at h
  | some p =>
    rw [hf] at h
    exact ⟨p.1, p.2, h⟩

theorem mem_shortGens {cap : Nat} {gens : List Nat} : ∀ g ∈ shortGens cap gens, g ∈ gens := by
  unfold shortGens
  have key : ∀ (l acc : List Nat), (∀ x ∈ acc, x ∈ gens) → (∀ x ∈ l, x ∈ gens) →
      ∀ x ∈ l.foldl (fun (acc : List Nat) g =>
        if (closW acc (cap + 1)).contains g then acc else acc ++ [g]) acc, x ∈ gens := by
    intro l
    induction l with
    | nil => intro acc h1 _; exact h1
    | cons y l ih =>
      intro acc h1 h2
      simp only [List.foldl_cons]
      refine ih _ ?_ (fun x hx => h2 x (List.mem_cons_of_mem _ hx))
      split_ifs
      · exact h1
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact h1 x hx
        · rw [List.mem_singleton.1 hx]; exact h2 y List.mem_cons_self
  exact key gens [] (by simp) (fun x hx => hx)

theorem survGensK_mem (S : KSetting H K Q T κ) {N Pl : List Nat} {tab : HashMap Nat Nat}
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ n ∈ N) (D : FrData H Q (Phi' Q) 6)
    (hD : ∀ x, D.wc x = tab.getD (κ x) 0) (hkg : kgensOK T = true)
    (hrep : repOK T N Pl 6 tab = true) :
    ∀ y ∈ survGensK T N Pl 6 tab, pkSet D.rho.range y := by
  intro y hy
  unfold survGensK at hy
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
  have hgl : g ∈ klist T := by
    have := kgensOK_spec hkg g hg
    unfold klist; exact List.mem_range.2 this
  obtain ⟨k, hk, hkg'⟩ := S.hκ.surj g hgl
  have hkH : k ∈ H := S.hKH hk
  refine ⟨D.rho ⟨k, hkH⟩, ⟨⟨k, hkH⟩, rfl⟩, ?_⟩
  rw [pk_def]
  congr 1
  apply List.ext_getElem
  · rw [length_colsOf]; simp
  · intro i h1 h2
    have hi : i < 6 := by simpa [length_colsOf] using h1
    rw [getElem_colsOf _ i hi]
    simp only [List.getElem_map, List.getElem_range]
    obtain ⟨hmem, htab⟩ := repOK_spec hrep i hi
    obtain ⟨q, hq, hqκ⟩ := (hQN _).2 hmem
    have hwq : D.wc q = 2 ^ i := by rw [hD q, hqκ]; exact htab
    have h3 := D.rho_of_mem ⟨k, hkH⟩ hq
    have e : (⟨D.wc q, D.wc_lt q hq⟩ : Fin (2 ^ 6)) =
        ⟨2 ^ i, Nat.pow_lt_pow_right (by norm_num) hi⟩ := Fin.ext hwq
    rw [e] at h3
    rw [h3, hD, S.hκ.conj S.hinv.elim hk (S.hQK hq), hkg', hqκ]

theorem survivor_core (S : KSetting H K Q T κ) {N : List Nat} (hNnd : N.Nodup)
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ n ∈ N) {zN : Nat} {z : G}
    (hzH : ∀ h ∈ H, h * z * h⁻¹ = z) (hzK : z ∈ K) (hκz : κ z = zN)
    (hsurv : survOK T N zN = true) :
    ∃ (tab : HashMap Nat Nat) (D : FrData H Q (Phi' Q) 6) (φ : Nat → Nat) (Sn : Node)
      (N1 N2 : List Nat), (∀ x, D.wc x = tab.getD (κ x) 0) ∧ D.rho.range ≤ Sig 6 φ ∧
      (∀ y, pkSet D.rho.range y ↔ y ∈ Sn.elems) ∧ Sn.elems.Nodup ∧
      vlCheck T N tab Sn N1 N2 = true ∧ plOK T (phiList T N) = true ∧
      (phiList T N).length = 2 ∧ zN ∈ phiList T N ∧ zN ≠ oneN T ∧ mulN T zN zN = oneN T ∧
      eCheck T N (phiList T N) zN = true ∧ N.length = 128 := by
  classical
  obtain ⟨Pl, d, typ, tab, pt, hPl, hpt, hchk⟩ := survOK_unfold hsurv
  obtain ⟨cap, sigP, gensK, sg, S0, nodes, hcap, hsigP, hgensK, hsg, hS0def, hnodes, hd, htyp, hpl,
    hfr, hphiOK, hl2, hzmem, hzne, hzsq, hnek, hmod, hj, hkg, hrep, hS0len, hlat, hE, hverd⟩ :=
    survCheck_spec hchk
  subst hPl
  subst hd
  subst htyp
  obtain ⟨D, hD⟩ := frData_of_lists S hQN hfr hpl
  have hphi : ∀ x ∈ Q, phiFn pt (D.wc x) = lamOf z Q 1 x := by
    intro x hx
    have hxN : κ x ∈ N := (hQN _).1 ⟨x, hx, rfl⟩
    have h1 := (List.all_eq_true.1 (by
      have := hphiOK
      unfold phiOK at this
      rw [← hpt] at this
      exact this)) (κ x) hxN
    rw [beq_iff_eq] at h1
    rw [hD x, h1]
    exact labelOf_eq S hQN hpl hzK hκz 1 hx
  have hlam : ∀ h ∈ H, ∀ x ∈ Q, lamOf z Q 1 (h * x * h⁻¹) = lamOf z Q 1 x :=
    fun h hh x hx => lamOf_inv hzH S.hQn 1 hh hx
  have hR : D.rho.range ≤ Sig 6 (phiFn pt) := D.range_le_Sig (phiFn pt) (lamOf z Q 1) hphi hlam
  have hNfr := Phi'_frattini S.hQ2
  have hcardH : Nat.card H = Nat.card Q * Nat.card D.rho.range :=
    D.card_H S.hQmax S.hQ2 S.hC hNfr
  have hKcard : Nat.card K = (klist T).length := S.hκ.card_eq
  have hQcard : Nat.card Q = N.length := card_of_codes S.hκ S.hQK hNnd hQN
  have hm : K.relIndex H * Nat.card K = Nat.card H := by
    have := Subgroup.relIndex_mul_card (H := K) (K := H)
    rwa [inf_eq_left.2 S.hKH] at this
  have hn : 0 < N.length := by rw [← hQcard]; exact Nat.card_pos
  obtain ⟨hNlen, -⟩ := frOK_spec T N hfr
  set n := N.length with hn_def
  set kk := (klist T).length with hkk
  set e := kk / n with he
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · exfalso
      have : kk = 0 := by rw [← hnek, h0]; simp
      have hKpos : 0 < Nat.card K := Nat.card_pos
      omega
    · exact h0
  set m := K.relIndex H with hmdef
  have hR_eq : Nat.card D.rho.range = m * e := by
    have h1 : n * Nat.card D.rho.range = n * (m * e) := by
      have a1 : Nat.card H = n * Nat.card D.rho.range := by rw [hcardH, hQcard]
      have a2 : Nat.card H = m * (n * e) := by rw [← hm, hKcard, hnek]
      calc n * Nat.card D.rho.range = m * (n * e) := a1.symm.trans a2
        _ = n * (m * e) := by ring
    exact Nat.eq_of_mul_eq_mul_left hn h1
  have hsigcard : Nat.card ↥(Sig 6 (phiFn pt)) = (sigList 6 (phiFn pt)).length := card_Sig 6 _
  have hdvd : m * e ∣ (sigList 6 (phiFn pt)).length := by
    rw [← hsigcard, ← hR_eq]
    exact Subgroup.card_dvd_of_le hR
  set s := (sigList 6 (phiFn pt)).length with hs
  have hse : s = e * (s / e) := by
    have := Nat.div_add_mod s e
    rw [hmod] at this; omega
  have hmdiv : m ∣ s / e := by
    have h1 : m * e ∣ e * (s / e) := by rw [← hse]; exact hdvd
    rw [mul_comm m e] at h1
    exact Nat.dvd_of_mul_dvd_mul_left hepos h1
  have hmodd : ¬ 2 ∣ m := S.hodd
  have hm1 : m ≠ 1 := by
    intro h1
    exact S.hne (Subgroup.relIndex_eq_one.1 h1)
  have hcop : ∀ k : Nat, Nat.Coprime m (2 ^ k) := fun k =>
    Nat.Coprime.pow_right k
      ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hmodd)))
  obtain ⟨j, hjlt, hj'⟩ := hj
  have hm105 : m ∣ 105 := by
    rw [hj'] at hmdiv
    exact (hcop j).dvd_of_dvd_mul_right hmdiv
  have hmle : m ≤ 105 := Nat.le_of_dvd (by norm_num) hm105
  have hcapR : Nat.card D.rho.range ≤ cap := by
    rw [hR_eq, hcap]
    calc m * e ≤ 105 * e := Nat.mul_le_mul_right e hmle
      _ = e * 105 := by ring
  have hgenS : ∀ y ∈ sg, pkSet D.rho.range y := by
    intro y hy
    apply survGensK_mem S hQN D hD hkg hrep y
    rw [← hgensK]
    rw [hsg] at hy
    exact mem_shortGens y hy
  have hS0R : ∀ y ∈ S0.elems, pkSet D.rho.range y := by
    intro y hy
    subst hS0def
    have hy' : y ∈ sortSet (closW sg (cap + 1)) := hy
    rw [mem_sortSet] at hy'
    unfold closW at hy'
    refine bfs_inv (pkSet D.rho.range) _ ?_ (oneS :: sg) ?_ _ y hy'
    · intro f hf x hx
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
      exact pkSet_mul hR hx (hgenS g hg)
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact pkSet_one
      · exact hgenS x hx
  have hsigP1 : ∀ σ ∈ Sig 6 (phiFn pt), pk σ ∈ sigP := by
    intro σ hσ
    rw [hsigP]
    exact List.mem_map.2 ⟨colsOf σ, colsOf_mem_sigList hσ, (pk_def σ).symm⟩
  have hsigP2 : ∀ y ∈ sigP, ∃ σ ∈ Sig 6 (phiFn pt), pk σ = y := by
    intro y hy
    rw [hsigP] at hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
    obtain ⟨σ, hσ, rfl⟩ := exists_of_mem_sigList hc
    exact ⟨σ, hσ, pk_def σ⟩
  obtain ⟨Sn, hSnmem, hSn⟩ := lattice_complete hR hcapR hsigP1 hsigP2 hlat hS0R
  have hSnnd : Sn.elems.Nodup := nodeValidW_nodup (latOK_valid hlat Sn hSnmem)
  have hcardR : Nat.card D.rho.range = Sn.elems.length := card_range_eq_of_pkSet hR hSnnd hSn
  have hN128 : N.length = 128 := by
    rw [← hn_def, hNlen, hl2]
    all_goals norm_num
  rcases hverd Sn hSnmem with hS0eq | heven | hv
  · exfalso
    rw [hS0eq, hS0len] at hcardR
    rw [hR_eq] at hcardR
    have : m * e = 1 * e := by rw [hcardR, one_mul]
    exact hm1 (Nat.eq_of_mul_eq_mul_right hepos this)
  · exfalso
    rw [← hcardR, hR_eq, Nat.mul_div_cancel _ hepos] at heven
    exact hmodd (Nat.dvd_of_mod_eq_zero heven)
  · obtain ⟨N1, N2, hvl⟩ := vlOK_spec hv
    exact ⟨tab, D, phiFn pt, Sn, N1, N2, hD, hR, hSn, hSnnd, hvl, hpl, hl2, hzmem, hzne, hzsq,
      hE, hN128⟩

theorem branch_surv {z : G} (S : KSetting H K Q T κ) (hHz : H = Gz z) (hQeq : Q = pCoreOf 2 H)
    (hzK : z ∈ K) {zN : Nat} (hκz : κ z = zN) {N : List Nat} (hNnd : N.Nodup)
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ n ∈ N) (hsurv : survOK T N zN = true) : StructAt G z := by
  classical
  have hzc : ∀ h ∈ H, h * z = z * h := by
    intro h hh
    rw [hHz] at hh
    exact ((Subgroup.mem_centralizer_iff.1 hh) z (Set.mem_singleton z)).symm
  have hzH : ∀ h ∈ H, h * z * h⁻¹ = z := by
    intro h hh
    rw [mul_inv_eq_iff_eq_mul]
    exact hzc h hh
  obtain ⟨tab, D, φ, Sn, N1, N2, hD, hR, hS, hSnnd, hvl, hpl, hl2, hzmem, hzne, hzsq, hE, hNlen⟩ :=
    survivor_core S hNnd hQN hzH hzK hκz hsurv
  have hext := surv_extraspecial S hzK hzc hκz hQN hpl D hl2 hzmem hzne hzsq hE
  obtain ⟨hzΦ, hΦeq⟩ := surv_phi S hzK hκz hQN hpl hl2 hzmem hzne
  obtain ⟨hlen, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hmul, hdet, hid⟩ := vlCheck_spec hvl
  obtain ⟨f, hfs, hfk⟩ :=
    exists_sl_hom D hR S.hQmax S.hQ2 S.hC hSnnd hS (basis3 N1) hlen hmul hdet hid
  obtain ⟨A, B, hAab, hBab, hAc, hBc, hABQ, hABz, hAn, hBn⟩ :=
    exists_AB S hNnd hQN hD hzΦ hΦeq hR hS hvl
  have hcard : Nat.card ↥Q = 128 := by
    rw [card_of_codes S.hκ S.hQK hNnd hQN]; exact hNlen
  subst hQeq
  subst hHz
  refine ⟨hext, hcard, ?_, ⟨f, hfs, hfk⟩, A, B, hAab, hBab, hAc, hBc, hABQ, hABz, hAn, hBn⟩
  intro x hx
  exact S.hC x hx.1 (fun y hy => ((Subgroup.mem_centralizer_iff.1 hx.2) y hy).symm)

end Branch

end CFSG.Quasithin.H13.I1277

end
