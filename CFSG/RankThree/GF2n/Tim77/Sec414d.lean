module

public import CFSG.RankThree.GF2n.Tim77.Sec414b
public import CFSG.RankThree.GF2n.Tim77.Sec414Ash
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def sec414W (V : Subgroup G) : Subgroup G := (CFSG.pCore 2 ↥V).map V.subtype

theorem sec414W_isPGroup (V : Subgroup G) : IsPGroup 2 ↥(sec414W V) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥V)).map V.subtype

theorem sec414W_conj {V : Subgroup G} {v p : G} (hv : v ∈ V) (hp : p ∈ sec414W V) :
    v * p * v⁻¹ ∈ sec414W V := by
  obtain ⟨q, hq, rfl⟩ := hp
  exact ⟨⟨v, hv⟩ * q * ⟨v, hv⟩⁻¹,
    (CFSG.pCore_normal (p := 2) (G := ↥V)).conj_mem q hq ⟨v, hv⟩, rfl⟩

theorem mem_sec414W_iff {V : Subgroup G} {x : G} (hx : x ∈ V) :
    x ∈ sec414W V ↔ Sec414InO2 V x := by
  rw [sec414_inO2_iff hx]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem sec414_mem_pCore_iff {V : Subgroup G} (y : ↥V) :
    y ∈ CFSG.pCore 2 ↥V ↔ (y : G) ∈ sec414W V := by
  rw [mem_sec414W_iff y.2, sec414_inO2_iff y.2]

theorem sec414_inO2_of_mem_W {V X : Subgroup G} (hXV : X ≤ V) {t : G} (htX : t ∈ X)
    (htW : t ∈ sec414W V) : Sec414InO2 X t := by
  refine ⟨X ⊓ sec414W V, inf_le_left, (sec414W_isPGroup V).to_le inf_le_right, ?_, ⟨htX, htW⟩⟩
  intro v hv p hp
  exact ⟨X.mul_mem (X.mul_mem hv hp.1) (X.inv_mem hv), sec414W_conj (hXV hv) hp.2⟩

theorem sec414_isPGroup_zpowers {z : G} (hz : z * z = 1) : IsPGroup 2 ↥(Subgroup.zpowers z) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_card, Nat.card_zpowers]
  have hdvd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

theorem sec414_mem_W_of_central {V : Subgroup G} {z : G} (hzV : z ∈ V) (hz2 : z * z = 1)
    (hc : ∀ w ∈ V, z * w = w * z) : z ∈ sec414W V := by
  rw [mem_sec414W_iff hzV]
  refine ⟨Subgroup.zpowers z, Subgroup.zpowers_le.mpr hzV, sec414_isPGroup_zpowers hz2, ?_,
    Subgroup.mem_zpowers z⟩
  intro v hv p hp
  have hcomm : Commute z v := (hc v hv)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
  have : v * z ^ k * v⁻¹ = z ^ k := by
    rw [mul_inv_eq_iff_eq_mul]
    exact ((hcomm.zpow_left k).eq).symm
  rw [this]
  exact Subgroup.zpow_mem_zpowers z k

theorem sec414_conj_le_of_mem {T V : Subgroup G} (hTV : T ≤ V) {u : G} (hu : u ∈ V) :
    conjSubgroup u T ≤ V := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := (mem_conjSubgroup_exists_t77 u T y).1 hy
  exact V.mul_mem (V.mul_mem hu (hTV ha)) (V.inv_mem hu)

structure Sec414Min (A A0 : Subgroup G) (g : G) : Prop where
  bad : ¬ ∀ x ∈ A0, Sec414InO2 (A ⊔ conjSubgroup g A) x
  mem : g ∈ A ⊔ conjSubgroup g A
  min : ∀ h : G, (¬ ∀ x ∈ A0, Sec414InO2 (A ⊔ conjSubgroup h A) x) →
    Nat.card ↥(A ⊔ conjSubgroup g A) ≤ Nat.card ↥(A ⊔ conjSubgroup h A)

theorem Sec414Sys.linked_not_comm {A A0 : Subgroup G} (S : Sec414Sys A A0) {C : Subgroup G}
    (h : normalizerIn A C = A0) : ¬ Sec414Comm A C := by
  intro hc
  apply S.a0_ne_A
  apply le_antisymm S.a0_le
  intro a ha
  rw [← h]
  exact Subgroup.mem_inf.mpr ⟨ha, le_normalizer_of_comm (fun x hx y hy => hc x hx y hy) ha⟩

namespace Sec414Min

variable {A A0 : Subgroup G} {g : G} (M : Sec414Min A A0 g)
include M

theorem inO2_of_lt {g₁ g₂ : G}
    (hlt : Nat.card ↥(conjSubgroup g₁ A ⊔ conjSubgroup g₂ A) <
      Nat.card ↥(A ⊔ conjSubgroup g A)) :
    ∀ x ∈ conjSubgroup g₁ A0, Sec414InO2 (conjSubgroup g₁ A ⊔ conjSubgroup g₂ A) x := by
  intro x hx
  by_contra hxn
  have hjoin : conjSubgroup g₁ (A ⊔ conjSubgroup (g₁⁻¹ * g₂) A) =
      conjSubgroup g₁ A ⊔ conjSubgroup g₂ A := by
    rw [conjSubgroup_sup_t77, ← conjSubgroup_mul, mul_inv_cancel_left]
  have hbad : ¬ ∀ y ∈ A0, Sec414InO2 (A ⊔ conjSubgroup (g₁⁻¹ * g₂) A) y := by
    intro hall
    obtain ⟨y, hy, rfl⟩ := (mem_conjSubgroup_exists_t77 g₁ A0 x).1 hx
    apply hxn
    have := sec414_inO2_conj g₁ (hall y hy)
    rwa [hjoin] at this
  have h1 := M.min _ hbad
  have hcard : Nat.card ↥(A ⊔ conjSubgroup (g₁⁻¹ * g₂) A) =
      Nat.card ↥(conjSubgroup g₁ A ⊔ conjSubgroup g₂ A) := by
    rw [← hjoin, card_conjSubgroup]
  omega

theorem sup_le_V {g₁ g₂ : G} (h₁ : g₁ ∈ A ⊔ conjSubgroup g A) (h₂ : g₂ ∈ A ⊔ conjSubgroup g A) :
    conjSubgroup g₁ A ⊔ conjSubgroup g₂ A ≤ A ⊔ conjSubgroup g A :=
  sup_le (sec414_conj_le_of_mem le_sup_left h₁) (sec414_conj_le_of_mem le_sup_left h₂)

theorem lt_of_ne {g₁ g₂ : G} (h₁ : g₁ ∈ A ⊔ conjSubgroup g A) (h₂ : g₂ ∈ A ⊔ conjSubgroup g A)
    (hne : conjSubgroup g₁ A ⊔ conjSubgroup g₂ A ≠ A ⊔ conjSubgroup g A) :
    Nat.card ↥(conjSubgroup g₁ A ⊔ conjSubgroup g₂ A) < Nat.card ↥(A ⊔ conjSubgroup g A) :=
  Subgroup.card_lt_of_lt (lt_of_le_of_ne (M.sup_le_V h₁ h₂) hne)

theorem free (S : Sec414Sys A A0) :
    normalizerIn A (conjSubgroup g A) = ⊥ ∧ normalizerIn (conjSubgroup g A) A = ⊥ ∧
      ¬ Sec414Comm A (conjSubgroup g A) := by
  rcases S.rel g with hc | ⟨hl, hl'⟩ | hf
  · exfalso
    apply M.bad
    intro x hx
    have hV : IsPGroup 2 ↥(A ⊔ conjSubgroup g A) :=
      sec414_isPGroup_sup S.elem.isPGroup (isElemAbelian_conj S.elem g).isPGroup
        (fun q hq p hp => by rw [← hc p hp q hq, mul_inv_cancel_right]; exact hp)
    exact ⟨A ⊔ conjSubgroup g A, le_rfl, hV, fun v hv p hp =>
      (A ⊔ conjSubgroup g A).mul_mem ((A ⊔ conjSubgroup g A).mul_mem hv hp)
        ((A ⊔ conjSubgroup g A).inv_mem hv), Subgroup.mem_sup_left (S.a0_le hx)⟩
  · exfalso
    apply M.bad
    intro x hx
    have hN : normalizerIn A (conjSubgroup g A) ≠ ⊥ := by rw [hl]; exact S.a0_ne
    have S3 := sec414_prop24 S.elem S.ti ⟨g, rfl⟩ hN (S.linked_not_comm hl)
    have hM : IsPGroup 2 ↥(normalizerIn A (conjSubgroup g A) ⊔ normalizerIn (conjSubgroup g A) A) :=
      S3.isElemAbelian_M.isPGroup
    refine ⟨normalizerIn A (conjSubgroup g A) ⊔ normalizerIn (conjSubgroup g A) A,
      S3.M_le_X, hM, ?_, Subgroup.mem_sup_left (hl ▸ hx)⟩
    intro v hv p hp
    exact (Subgroup.mem_normalizer_iff.mp (S3.sup_le_normalizer_M hv) p).mp hp
  · exact ⟨hf.1, hf.2.1, hf.2.2⟩

theorem inf_W (S : Sec414Sys A A0) {t : G} (ht : t ∈ A)
    (htW : t ∈ sec414W (A ⊔ conjSubgroup g A)) : t = 1 := by
  by_contra ht1
  have hN := (M.free S).1
  have hO : Sec414InO2 (conjSubgroup 1 A ⊔ conjSubgroup g A) t := by
    rw [conjSubgroup_one]
    exact sec414_inO2_of_mem_W le_rfl (Subgroup.mem_sup_left ht) htW
  have hnorm := S.mem_normalizer_of_inO2 1 g (by rwa [conjSubgroup_one]) ht1 hO
  have : t ∈ normalizerIn A (conjSubgroup g A) := Subgroup.mem_inf.mpr ⟨ht, hnorm⟩
  rw [hN, Subgroup.mem_bot] at this
  exact ht1 this

theorem sup_eq_of_normalizerIn (S : Sec414Sys A A0) {g₁ g₂ : G}
    (h₁ : g₁ ∈ A ⊔ conjSubgroup g A) (h₂ : g₂ ∈ A ⊔ conjSubgroup g A)
    (hN : normalizerIn (conjSubgroup g₁ A) (conjSubgroup g₂ A) = ⊥) :
    conjSubgroup g₁ A ⊔ conjSubgroup g₂ A = A ⊔ conjSubgroup g A := by
  by_contra hne
  have hin := M.inO2_of_lt (M.lt_of_ne h₁ h₂ hne)
  obtain ⟨⟨x, hx⟩, hx1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (S.conj g₁).a0_ne
  have hx1 : x ≠ 1 := fun e => hx1' (Subtype.ext e)
  have hxA : x ∈ conjSubgroup g₁ A := (S.conj g₁).a0_le hx
  have hnorm := S.mem_normalizer_of_inO2 g₁ g₂ hxA hx1 (hin x hx)
  have : x ∈ normalizerIn (conjSubgroup g₁ A) (conjSubgroup g₂ A) :=
    Subgroup.mem_inf.mpr ⟨hxA, hnorm⟩
  rw [hN, Subgroup.mem_bot] at this
  exact hx1 this

end Sec414Min

@[expose] def Sec414EG (A A0 V : Subgroup G) (x : G) : Prop :=
  ∃ u ∈ V, ∃ a ∈ A, a ∉ A0 ∧ x = u * a * u⁻¹

namespace Sec414Min

variable {A A0 : Subgroup G} {g : G} (M : Sec414Min A A0 g)
include M

theorem pow_mem_W (S : Sec414Sys A A0) {x y : G}
    (hx : Sec414EG A A0 (A ⊔ conjSubgroup g A) x) (hy : Sec414EG A A0 (A ⊔ conjSubgroup g A) y)
    {n : ℕ} (hn : Odd n) (hn1 : n ≠ 1) (hord : orderOf (x * y) = 2 * n) :
    (x * y) ^ n ∈ sec414W (A ⊔ conjSubgroup g A) := by
  obtain ⟨u, hu, a, ha, ha0, rfl⟩ := hx
  obtain ⟨v, hv, b, hb, hb0, rfl⟩ := hy
  have hAV : A ≤ A ⊔ conjSubgroup g A := le_sup_left
  have hxD : u * a * u⁻¹ ∈ Sec414D A A0 := ⟨u, a, ha, ha0, rfl⟩
  have hyD : v * b * v⁻¹ ∈ Sec414D A A0 := ⟨v, b, hb, hb0, rfl⟩
  have hxA : u * a * u⁻¹ ∈ conjSubgroup u A := (mem_conjSubgroup_conj_t77 u a A).2 ha
  have hyA : v * b * v⁻¹ ∈ conjSubgroup v A := (mem_conjSubgroup_conj_t77 v b A).2 hb
  have hAv : conjSubgroup (v * u⁻¹) (conjSubgroup u A) = conjSubgroup v A := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  have hAv0 : conjSubgroup (v * u⁻¹) (conjSubgroup u A0) = conjSubgroup v A0 := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  have hrel := (S.conj u).rel (v * u⁻¹)
  rw [hAv, hAv0] at hrel
  rcases hrel with hcomm | ⟨hlink, hlink'⟩ | ⟨hfree, -, -⟩
  · exfalso
    have hxy : u * a * u⁻¹ * (v * b * v⁻¹) = v * b * v⁻¹ * (u * a * u⁻¹) := hcomm _ hxA _ hyA
    have hsq : (u * a * u⁻¹ * (v * b * v⁻¹)) * (u * a * u⁻¹ * (v * b * v⁻¹)) = 1 := by
      calc _ = (u * a * u⁻¹) * ((v * b * v⁻¹) * (u * a * u⁻¹)) * (v * b * v⁻¹) := by group
        _ = (u * a * u⁻¹) * ((u * a * u⁻¹) * (v * b * v⁻¹)) * (v * b * v⁻¹) := by rw [← hxy]
        _ = ((u * a * u⁻¹) * (u * a * u⁻¹)) * ((v * b * v⁻¹) * (v * b * v⁻¹)) := by group
        _ = 1 := by rw [S.D_sq hxD, S.D_sq hyD, one_mul]
    have h2 : orderOf (u * a * u⁻¹ * (v * b * v⁻¹)) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    rw [hord] at h2
    have h3 : 2 * n ∣ 2 * 1 := by rwa [mul_one]
    have : n ∣ 1 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) h3
    exact hn1 (Nat.dvd_one.mp this)
  · exfalso
    have hN : normalizerIn (conjSubgroup u A) (conjSubgroup v A) ≠ ⊥ := by
      rw [hlink]; exact (S.conj u).a0_ne
    have hnc := (S.conj u).linked_not_comm hlink
    have S3 := sec414_prop24 (S.conj u).elem (S.conj u).ti ⟨v * u⁻¹, hAv.symm⟩ hN hnc
    have hodd := S3.odd_orderOf_mul hxA
      (fun h => ha0 ((mem_conjSubgroup_conj_t77 u a A0).1 (hlink ▸ h))) hyA
      (fun h => hb0 ((mem_conjSubgroup_conj_t77 v b A0).1 (hlink' ▸ h)))
    rw [hord] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  · have hsup := M.sup_eq_of_normalizerIn S hu hv hfree
    obtain ⟨hz1, hz2⟩ := S.pow_centralizes ha ha0 hb hb0 hn hord
    have hxV : u * a * u⁻¹ ∈ A ⊔ conjSubgroup g A :=
      (A ⊔ conjSubgroup g A).mul_mem ((A ⊔ conjSubgroup g A).mul_mem hu (hAV ha))
        ((A ⊔ conjSubgroup g A).inv_mem hu)
    have hyV : v * b * v⁻¹ ∈ A ⊔ conjSubgroup g A :=
      (A ⊔ conjSubgroup g A).mul_mem ((A ⊔ conjSubgroup g A).mul_mem hv (hAV hb))
        ((A ⊔ conjSubgroup g A).inv_mem hv)
    have hzV : (u * a * u⁻¹ * (v * b * v⁻¹)) ^ n ∈ A ⊔ conjSubgroup g A :=
      (A ⊔ conjSubgroup g A).pow_mem ((A ⊔ conjSubgroup g A).mul_mem hxV hyV) n
    have hz2' : (u * a * u⁻¹ * (v * b * v⁻¹)) ^ n * (u * a * u⁻¹ * (v * b * v⁻¹)) ^ n = 1 := by
      rw [← pow_add, ← two_mul]; exact hord ▸ pow_orderOf_eq_one _
    refine sec414_mem_W_of_central hzV hz2' fun w hw => ?_
    rw [← hsup] at hw
    have hle : conjSubgroup u A ⊔ conjSubgroup v A ≤
        Subgroup.centralizer ({(u * a * u⁻¹ * (v * b * v⁻¹)) ^ n} : Set G) := by
      refine sup_le (fun c hc => ?_) (fun c hc => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact (hz1 c hc).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact (hz2 c hc).symm
    exact (Subgroup.mem_centralizer_iff.mp (hle hw) _ (Set.mem_singleton _))

theorem pair_conj (S : Sec414Sys A A0) {a e : G} (ha : a ∈ A) (ha0 : a ∉ A0)
    (he : e ∈ conjSubgroup g A) (he0 : e ∉ conjSubgroup g A0) :
    ∃ c ∈ A ⊔ conjSubgroup g A, c * a * c⁻¹ * e⁻¹ ∈ sec414W (A ⊔ conjSubgroup g A) := by
  have hAV : A ≤ A ⊔ conjSubgroup g A := le_sup_left
  have hBV : conjSubgroup g A ≤ A ⊔ conjSubgroup g A := le_sup_right
  have haD : a ∈ Sec414D A A0 := ⟨1, a, ha, ha0, by group⟩
  have heD : e ∈ Sec414D A A0 := S.mem_D_of_conj he he0
  have ha2 := S.D_sq haD
  have he2 := S.D_sq heD
  have hxy : a * e ≠ e * a := fun h => (M.free S).2.2 (S.comm_of_commute ha ha0 g he he0 h)
  have hcl : Subgroup.closure ({a, e} : Set G) ≤ A ⊔ conjSubgroup g A := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hAV ha
    · exact hBV he
  have hF1 := S.not_four_dvd haD heD
  rcases Nat.even_or_odd (orderOf (a * e)) with ⟨k, hk⟩ | hodd
  · have hkodd : Odd k := by
      by_contra hke
      rw [Nat.not_odd_iff_even] at hke
      obtain ⟨j, hj⟩ := hke
      exact hF1 ⟨j, by omega⟩
    have hk1 : k ≠ 1 := by
      rintro rfl
      apply hxy
      have h2 : (a * e) * (a * e) = 1 := by
        rw [← pow_two]
        have := pow_orderOf_eq_one (a * e)
        rwa [hk] at this
      exact sec48_comm_of_sq ha2 he2 h2
    obtain ⟨a', ha', rfl⟩ := (mem_conjSubgroup_exists_t77 g A e).1 he
    have ha'0 : a' ∉ A0 := fun h => he0 ((mem_conjSubgroup_conj_t77 g a' A0).2 h)
    have hzW := M.pow_mem_W S (x := a) (y := g * a' * g⁻¹)
      ⟨1, (A ⊔ conjSubgroup g A).one_mem, a, ha, ha0, by group⟩ ⟨g, M.mem, a', ha', ha'0, rfl⟩
      hkodd hk1 (by omega)
    obtain ⟨j, rfl⟩ := hkodd
    have hdih := sec414_dihedral_pow_odd ha2 he2 j
    have hz1 : ((a * (g * a' * g⁻¹)) ^ (2 * j + 1)) * ((a * (g * a' * g⁻¹)) ^ (2 * j + 1)) = 1 := by
      rw [← pow_add, ← two_mul]
      have := pow_orderOf_eq_one (a * (g * a' * g⁻¹))
      rw [hk] at this
      rw [show 2 * (2 * j + 1) = (2 * j + 1) + (2 * j + 1) by ring]
      exact this
    refine ⟨(a * (g * a' * g⁻¹)) ^ j, (A ⊔ conjSubgroup g A).pow_mem
      ((A ⊔ conjSubgroup g A).mul_mem (hAV ha) (hBV he)) j, ?_⟩
    set r := a * (g * a' * g⁻¹) with hr
    set z := r ^ (2 * j + 1) with hz
    set c := r ^ j with hc
    have hcz : c * z * c⁻¹ = z := by
      have : c * z = z * c := (Commute.pow_pow_self r j (2 * j + 1)).eq
      rw [this]; group
    have h1 : c * (a * z) * c⁻¹ = g * a' * g⁻¹ := by
      rw [hdih]; group
    have h3 : c * a * c⁻¹ * z = g * a' * g⁻¹ := by
      calc c * a * c⁻¹ * z = c * a * c⁻¹ * (c * z * c⁻¹) := by rw [hcz]
        _ = c * (a * z) * c⁻¹ := by group
        _ = _ := h1
    have h2 : c * a * c⁻¹ = g * a' * g⁻¹ * z⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]; exact h3
    rw [h2]
    exact sec414W_conj (hBV he) ((sec414W _).inv_mem hzW)
  · obtain ⟨c, hc, hce⟩ := sec414_exists_conj_of_odd ha2 he2 hodd
    refine ⟨c, hcl hc, ?_⟩
    rw [← hce, mul_inv_cancel]
    exact (sec414W _).one_mem

theorem hprod_G (S : Sec414Sys A A0) {x y : G}
    (hx : Sec414EG A A0 (A ⊔ conjSubgroup g A) x) (hy : Sec414EG A A0 (A ⊔ conjSubgroup g A) y) :
    orderOf (x * y) ∣ 2 ∨ Odd (orderOf (x * y)) ∨
      ∃ n : ℕ, Odd n ∧ orderOf (x * y) = 2 * n ∧
        (x * y) ^ n ∈ sec414W (A ⊔ conjSubgroup g A) := by
  have hxD : x ∈ Sec414D A A0 := by
    obtain ⟨u, -, a, ha, ha0, rfl⟩ := hx
    exact ⟨u, a, ha, ha0, rfl⟩
  have hyD : y ∈ Sec414D A A0 := by
    obtain ⟨u, -, a, ha, ha0, rfl⟩ := hy
    exact ⟨u, a, ha, ha0, rfl⟩
  have hF1 := S.not_four_dvd hxD hyD
  rcases Nat.even_or_odd (orderOf (x * y)) with ⟨k, hk⟩ | hodd
  · by_cases hk1 : k = 1
    · left
      simp [hk, hk1]
    · right; right
      have hkodd : Odd k := by
        by_contra hke
        rw [Nat.not_odd_iff_even] at hke
        obtain ⟨j, hj⟩ := hke
        exact hF1 ⟨j, by omega⟩
      exact ⟨k, hkodd, by omega, M.pow_mem_W S hx hy hkodd hk1 (by omega)⟩
  · exact Or.inr (Or.inl hodd)

theorem hone_G (S : Sec414Sys A A0) {x y : G}
    (hx : Sec414EG A A0 (A ⊔ conjSubgroup g A) x) (hy : Sec414EG A A0 (A ⊔ conjSubgroup g A) y) :
    ∃ w ∈ A ⊔ conjSubgroup g A, w * x * w⁻¹ * y⁻¹ ∈ sec414W (A ⊔ conjSubgroup g A) := by
  obtain ⟨u, hu, a, ha, ha0, rfl⟩ := hx
  obtain ⟨v, hv, b, hb, hb0, rfl⟩ := hy
  obtain ⟨e₀, he₀, he₀0⟩ := (S.conj g).exists_not_mem
  obtain ⟨c₁, hc₁, h₁⟩ := M.pair_conj S ha ha0 he₀ he₀0
  obtain ⟨c₂, hc₂, h₂⟩ := M.pair_conj S hb hb0 he₀ he₀0
  refine ⟨v * c₂⁻¹ * c₁ * u⁻¹, ?_, ?_⟩
  · exact (A ⊔ conjSubgroup g A).mul_mem
      ((A ⊔ conjSubgroup g A).mul_mem ((A ⊔ conjSubgroup g A).mul_mem hv
        ((A ⊔ conjSubgroup g A).inv_mem hc₂)) hc₁) ((A ⊔ conjSubgroup g A).inv_mem hu)
  · have e : v * c₂⁻¹ * c₁ * u⁻¹ * (u * a * u⁻¹) * (v * c₂⁻¹ * c₁ * u⁻¹)⁻¹ * (v * b * v⁻¹)⁻¹ =
        v * (c₂⁻¹ * ((c₁ * a * c₁⁻¹ * e₀⁻¹) * (c₂ * b * c₂⁻¹ * e₀⁻¹)⁻¹) * c₂⁻¹⁻¹) * v⁻¹ := by
      group
    rw [e]
    refine sec414W_conj hv (sec414W_conj ((A ⊔ conjSubgroup g A).inv_mem hc₂) ?_)
    exact (sec414W _).mul_mem h₁ ((sec414W _).inv_mem h₂)

theorem comm_of_commute_E (S : Sec414Sys A A0) {a e f : G} (ha : a ∈ A) (ha0 : a ∉ A0)
    (he : Sec414EG A A0 (A ⊔ conjSubgroup g A) e) (hf : Sec414EG A A0 (A ⊔ conjSubgroup g A) f)
    (hea : e * a = a * e) (hfa : f * a = a * f) : e * f = f * e := by
  obtain ⟨v, hv, b, hb, hb0, rfl⟩ := he
  obtain ⟨w, hw, c, hc, hc0, rfl⟩ := hf
  have hAv : conjSubgroup (w * v⁻¹) (conjSubgroup v A) = conjSubgroup w A := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  have hAv0 : conjSubgroup (w * v⁻¹) (conjSubgroup v A0) = conjSubgroup w A0 := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  have hbA : v * b * v⁻¹ ∈ conjSubgroup v A := (mem_conjSubgroup_conj_t77 v b A).2 hb
  have hbA0 : v * b * v⁻¹ ∉ conjSubgroup v A0 :=
    fun h => hb0 ((mem_conjSubgroup_conj_t77 v b A0).1 h)
  have hcA : w * c * w⁻¹ ∈ conjSubgroup w A := (mem_conjSubgroup_conj_t77 w c A).2 hc
  have hcA0 : w * c * w⁻¹ ∉ conjSubgroup w A0 :=
    fun h => hc0 ((mem_conjSubgroup_conj_t77 w c A0).1 h)
  have hZv := S.comm_of_commute ha ha0 v hbA hbA0 hea.symm
  have hZw := S.comm_of_commute ha ha0 w hcA hcA0 hfa.symm
  have hle_v : conjSubgroup v A ≤ centralizer (A : Set G) := fun y hy =>
    Subgroup.mem_centralizer_iff.mpr (fun h hh => hZv h hh y hy)
  have hle_w : conjSubgroup w A ≤ centralizer (A : Set G) := fun y hy =>
    Subgroup.mem_centralizer_iff.mpr (fun h hh => hZw h hh y hy)
  have hrel := (S.conj v).rel (w * v⁻¹)
  rw [hAv, hAv0] at hrel
  rcases hrel with hcomm | ⟨hlink, hlink'⟩ | ⟨hfree, -, -⟩
  · exact hcomm _ hbA _ hcA
  · have hN : normalizerIn (conjSubgroup v A) (conjSubgroup w A) ≠ ⊥ := by
      rw [hlink]; exact (S.conj v).a0_ne
    have hnc := (S.conj v).linked_not_comm hlink
    have S3 := sec414_prop24 (S.conj v).elem (S.conj v).ti ⟨w * v⁻¹, hAv.symm⟩ hN hnc
    obtain ⟨x, hxX, hxeq⟩ := S3.exists_conj_eq
    have hxC : x ∈ centralizer (A : Set G) := (sup_le hle_v hle_w) hxX
    have hrt := S.rootCent v hle_v
    have hN' : normalizerIn (conjSubgroup v A) (conjSubgroup x (conjSubgroup v A)) ≠ ⊥ := by
      rw [← hxeq]; exact hN
    have h4 := hrt.2.2.2 x hxC hN'
    rw [← hxeq] at h4
    exact h4 _ hbA _ hcA
  · exfalso
    have hsup := M.sup_eq_of_normalizerIn S hv hw hfree
    have hBle : conjSubgroup g A ≤ centralizer (A : Set G) := by
      have : conjSubgroup v A ⊔ conjSubgroup w A ≤ centralizer (A : Set G) :=
        sup_le hle_v hle_w
      rw [hsup] at this
      exact le_sup_right.trans this
    apply (M.free S).2.2
    intro a' ha' y hy
    exact Subgroup.mem_centralizer_iff.mp (hBle hy) a' ha'

end Sec414Min

theorem Sec414Sys.comm_of_sq_mem_W {A A0 V : Subgroup G} (S : Sec414Sys A A0) {x y : G}
    (hx : x ∈ Sec414D A A0) (hy : y ∈ Sec414D A A0) (h : (x * y) ^ 2 ∈ sec414W V) :
    x * y = y * x := by
  have hF1 := S.not_four_dvd hx hy
  have hz2 : IsPGroup 2 ↥(Subgroup.zpowers ((x * y) ^ 2)) :=
    (sec414W_isPGroup V).to_le (Subgroup.zpowers_le.mpr h)
  obtain ⟨i, hi⟩ := (IsPGroup.iff_orderOf.mp hz2) ⟨(x * y) ^ 2, Subgroup.mem_zpowers _⟩
  rw [Subgroup.orderOf_mk] at hi
  have hsq : (x * y) ^ 2 = 1 := by
    rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · interval_cases i
      · exact orderOf_eq_one_iff.mp (by simpa using hi)
      · exfalso
        have h4 : ((x * y) ^ 2) ^ 2 = 1 := by
          have := pow_orderOf_eq_one ((x * y) ^ 2)
          rw [hi] at this
          simpa using this
        by_cases h1 : (x * y) ^ 2 = 1
        · rw [h1, orderOf_one] at hi
          norm_num at hi
        · exact hF1 (by rw [orderOf_eq_four h1 h4])
    · exfalso
      apply hF1
      have : orderOf ((x * y) ^ 2) ∣ orderOf (x * y) := orderOf_pow_dvd 2
      rw [hi] at this
      exact (pow_dvd_pow 2 hi2 : 2 ^ 2 ∣ 2 ^ i).trans this
  exact sec48_comm_of_sq (S.D_sq hx) (S.D_sq hy) (by rw [← pow_two]; exact hsq)

theorem sec414_isElemAbelian_closure {Γ : Type} [Group Γ] (T : Set Γ)
    (hsq : ∀ x ∈ T, x * x = 1) (hc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) :
    IsElemAbelian 2 (Subgroup.closure T) := by
  have hcomm : ∀ x ∈ Subgroup.closure T, ∀ y ∈ Subgroup.closure T, x * y = y * x := by
    intro x hx y hy
    refine Subgroup.closure_induction₂ (p := fun x y _ _ => x * y = y * x) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      hx hy
    · intro x y hx hy
      exact hc x hx y hy
    · intro x hx; simp
    · intro x hx; simp
    · intro x y z _ _ _ h1 h2
      calc x * y * z = x * (y * z) := by group
        _ = x * (z * y) := by rw [h2]
        _ = (x * z) * y := by group
        _ = (z * x) * y := by rw [h1]
        _ = z * (x * y) := by group
    · intro y z x _ _ _ h1 h2
      calc x * (y * z) = (x * y) * z := by group
        _ = (y * x) * z := by rw [h1]
        _ = y * (x * z) := by group
        _ = y * (z * x) := by rw [h2]
        _ = (y * z) * x := by group
    · intro x y _ _ h
      calc x⁻¹ * y = x⁻¹ * (y * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * y) * x⁻¹ := by rw [h]
        _ = y * x⁻¹ := by group
    · intro x y _ _ h
      calc x * y⁻¹ = y⁻¹ * (y * x) * y⁻¹ := by group
        _ = y⁻¹ * (x * y) * y⁻¹ := by rw [h]
        _ = y⁻¹ * x := by group
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
  rw [sq]
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hsq x hx
  | one => simp
  | mul x₁ x₂ hx₁ hx₂ ih₁ ih₂ =>
    calc x₁ * x₂ * (x₁ * x₂) = x₁ * (x₂ * x₁) * x₂ := by group
      _ = x₁ * (x₁ * x₂) * x₂ := by rw [hcomm x₂ hx₂ x₁ hx₁]
      _ = (x₁ * x₁) * (x₂ * x₂) := by group
      _ = 1 := by rw [ih₁, ih₂, one_mul]
  | inv x₁ _ ih =>
    calc x₁⁻¹ * x₁⁻¹ = (x₁ * x₁)⁻¹ := by group
      _ = 1 := by rw [ih, inv_one]

namespace Sec414Min

variable {A A0 : Subgroup G} {g : G} (M : Sec414Min A A0 g)
include M

theorem comm_of_commute_EG (S : Sec414Sys A A0) {d e f : G}
    (hd : Sec414EG A A0 (A ⊔ conjSubgroup g A) d) (he : Sec414EG A A0 (A ⊔ conjSubgroup g A) e)
    (hf : Sec414EG A A0 (A ⊔ conjSubgroup g A) f) (hed : e * d = d * e) (hfd : f * d = d * f) :
    e * f = f * e := by
  obtain ⟨u, hu, a, ha, ha0, rfl⟩ := hd
  have hconj : ∀ z : G, Sec414EG A A0 (A ⊔ conjSubgroup g A) z →
      Sec414EG A A0 (A ⊔ conjSubgroup g A) (u⁻¹ * z * u) := by
    rintro z ⟨v, hv, b, hb, hb0, rfl⟩
    refine ⟨u⁻¹ * v, (A ⊔ conjSubgroup g A).mul_mem ((A ⊔ conjSubgroup g A).inv_mem hu) hv, b, hb,
      hb0, by group⟩
  have hcomm : ∀ z : G, z * (u * a * u⁻¹) = (u * a * u⁻¹) * z →
      (u⁻¹ * z * u) * a = a * (u⁻¹ * z * u) := by
    intro z hz
    calc u⁻¹ * z * u * a = u⁻¹ * (z * (u * a * u⁻¹)) * u := by group
      _ = u⁻¹ * ((u * a * u⁻¹) * z) * u := by rw [hz]
      _ = a * (u⁻¹ * z * u) := by group
  have h := M.comm_of_commute_E S ha ha0 (hconj e he) (hconj f hf) (hcomm e hed) (hcomm f hfd)
  calc e * f = u * (u⁻¹ * e * u * (u⁻¹ * f * u)) * u⁻¹ := by group
    _ = u * (u⁻¹ * f * u * (u⁻¹ * e * u)) * u⁻¹ := by rw [h]
    _ = f * e := by group

end Sec414Min

theorem sec414_bender_of_min
    {A A0 : Subgroup G} {g : G} (S : Sec414Sys A A0) (M : Sec414Min A A0 g) :
    ∃ (K : Type) (_ : Group K) (π : ↥(A ⊔ conjSubgroup g A) →* K),
      CFSG.BenderSuzuki.IsBenderGroup K ∧ Function.Surjective π ∧
      (∀ a : ↥(A ⊔ conjSubgroup g A), (a : G) ∈ A → π a = 1 → a = 1) ∧
      (∀ y : ↥(A ⊔ conjSubgroup g A), y * y = 1 → π y = 1 →
        (y : G) ∈ sec414W (A ⊔ conjSubgroup g A)) := by
  set V : Subgroup G := A ⊔ conjSubgroup g A with hV
  have hAV : A ≤ V := le_sup_left
  have hBV : conjSubgroup g A ≤ V := le_sup_right
  set E : Set ↥V := {x | Sec414EG A A0 V (x : G)} with hEdef
  have hEmem : ∀ x : ↥V, x ∈ E ↔ Sec414EG A A0 V (x : G) := fun x => Iff.rfl
  have hED : ∀ x : ↥V, x ∈ E → (x : G) ∈ Sec414D A A0 := by
    intro x hx
    obtain ⟨u, -, a, ha, ha0, hx⟩ := (hEmem x).1 hx
    exact ⟨u, a, ha, ha0, hx⟩
  have hinv : ∀ (h x : ↥V), x ∈ E → h * x * h⁻¹ ∈ E := by
    intro h x hx
    obtain ⟨u, hu, a, ha, ha0, hx⟩ := (hEmem x).1 hx
    refine (hEmem _).2 ⟨(h : G) * u, V.mul_mem h.2 hu, a, ha, ha0, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx]
    group
  have hgen : Subgroup.closure E = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hmap : V ≤ (Subgroup.closure E).map V.subtype := by
      refine sup_le ?_ ?_
      · refine (le_of_eq S.closure_diff.symm).trans ((Subgroup.closure_le _).mpr ?_)
        rintro x ⟨hxA, hxA0⟩
        exact ⟨⟨x, hAV hxA⟩, Subgroup.subset_closure
          ((hEmem _).2 ⟨1, V.one_mem, x, hxA, hxA0, by simp⟩), rfl⟩
      · refine (le_of_eq (S.conj g).closure_diff.symm).trans ((Subgroup.closure_le _).mpr ?_)
        rintro x ⟨hxB, hxB0⟩
        obtain ⟨a, ha, rfl⟩ := (mem_conjSubgroup_exists_t77 g A x).1 hxB
        have ha0 : a ∉ A0 := fun h => hxB0 ((mem_conjSubgroup_conj_t77 g a A0).2 h)
        exact ⟨⟨g * a * g⁻¹, hBV hxB⟩, Subgroup.subset_closure
          ((hEmem _).2 ⟨g, M.mem, a, ha, ha0, rfl⟩), rfl⟩
    obtain ⟨z, hz, hzy⟩ := hmap y.2
    have : z = y := Subtype.ext hzy
    rwa [← this]
  have hsq : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    apply Subtype.ext
    show (x : G) * (x : G) = 1
    exact S.D_sq (hED x hx)
  have hnotW : ∀ x ∈ E, x ∉ CFSG.pCore 2 ↥V := by
    intro x hx hxW
    obtain ⟨u, hu, a, ha, ha0, hxu⟩ := (hEmem x).1 hx
    rw [sec414_mem_pCore_iff, hxu] at hxW
    have h1 := sec414W_conj (V.inv_mem hu) hxW
    rw [show u⁻¹ * (u * a * u⁻¹) * u⁻¹⁻¹ = a by group] at h1
    exact ha0 ((M.inf_W S ha h1) ▸ A0.one_mem)
  have hprod : ∀ x ∈ E, ∀ y ∈ E, orderOf (x * y) ∣ 2 ∨ Odd (orderOf (x * y)) ∨
      ∃ n : ℕ, Odd n ∧ orderOf (x * y) = 2 * n ∧ (x * y) ^ n ∈ CFSG.pCore 2 ↥V := by
    intro x hx y hy
    have ho : orderOf (x * y) = orderOf ((x : G) * (y : G)) := (Subgroup.orderOf_coe (x * y)).symm
    rw [ho]
    rcases M.hprod_G S ((hEmem x).1 hx) ((hEmem y).1 hy) with h | h | ⟨n, hn, hord, hW⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ⟨n, hn, hord, ?_⟩)
      rw [sec414_mem_pCore_iff]
      simpa using hW
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, (x * y) ^ 2 ∈ CFSG.pCore 2 ↥V → x * y = y * x := by
    intro x hx y hy h
    rw [sec414_mem_pCore_iff] at h
    apply Subtype.ext
    exact S.comm_of_sq_mem_W (V := V) (hED x hx) (hED y hy) (by simpa using h)
  have helem : ∀ d ∈ E, IsElemAbelian 2 (Subgroup.closure {e | e ∈ E ∧ e * d = d * e}) := by
    intro d hd
    refine sec414_isElemAbelian_closure _ (fun e he => hsq e he.1) ?_
    rintro e ⟨he, hed⟩ f ⟨hf, hfd⟩
    apply Subtype.ext
    exact M.comm_of_commute_EG S ((hEmem d).1 hd) ((hEmem e).1 he) ((hEmem f).1 hf)
      (congrArg Subtype.val hed) (congrArg Subtype.val hfd)
  have hnc : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x := by
    obtain ⟨a, ha, ha0⟩ := S.exists_not_mem
    have he : g * a * g⁻¹ ∈ conjSubgroup g A := (mem_conjSubgroup_conj_t77 g a A).2 ha
    have he0 : g * a * g⁻¹ ∉ conjSubgroup g A0 :=
      fun h => ha0 ((mem_conjSubgroup_conj_t77 g a A0).1 h)
    refine ⟨⟨a, hAV ha⟩, (hEmem _).2 ⟨1, V.one_mem, a, ha, ha0, by simp⟩,
      ⟨g * a * g⁻¹, hBV he⟩, (hEmem _).2 ⟨g, M.mem, a, ha, ha0, rfl⟩, fun h => ?_⟩
    exact (M.free S).2.2 (S.comm_of_commute ha ha0 g he he0 (congrArg Subtype.val h))
  have hone : ∀ x ∈ E, ∀ y ∈ E, ∃ w : ↥V, w * x * w⁻¹ * y⁻¹ ∈ CFSG.pCore 2 ↥V := by
    intro x hx y hy
    obtain ⟨w, hw, hW⟩ := M.hone_G S ((hEmem x).1 hx) ((hEmem y).1 hy)
    refine ⟨⟨w, hw⟩, ?_⟩
    rw [sec414_mem_pCore_iff]
    simpa using hW
  have hA : ∃ x ∈ E, ∃ y ∈ E, x * y = y * x ∧ x * y ∉ CFSG.pCore 2 ↥V := by
    obtain ⟨a, ha, ha0⟩ := S.exists_not_mem
    obtain ⟨⟨c, hc⟩, hc1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.a0_ne
    have hc1 : c ≠ 1 := fun e => hc1' (Subtype.ext e)
    have hac : a * c ∈ A := A.mul_mem ha (S.a0_le hc)
    have hac0 : a * c ∉ A0 := fun h => ha0 (by
      have := A0.mul_mem h (A0.inv_mem hc)
      rwa [mul_inv_cancel_right] at this)
    refine ⟨⟨a, hAV ha⟩, (hEmem _).2 ⟨1, V.one_mem, a, ha, ha0, by simp⟩, ⟨a * c, hAV hac⟩,
      (hEmem _).2 ⟨1, V.one_mem, a * c, hac, hac0, by simp⟩, ?_, ?_⟩
    · apply Subtype.ext
      exact S.comm_A ha hac
    · intro h
      rw [sec414_mem_pCore_iff] at h
      have hac' : a * (a * c) = c := by rw [← mul_assoc, S.sq_A ha, one_mul]
      have h' : c ∈ sec414W V := by simpa [hac'] using h
      exact hc1 (M.inf_W S (S.a0_le hc) h')
  have hQ := sec414_bender_quotient E hinv hgen hsq hnotW hprod hcomm helem hnc hone hA
  refine ⟨_, inferInstance, (QuotientGroup.mk' (Subgroup.center (↥V ⧸ CFSG.pCore 2 ↥V))).comp
    (QuotientGroup.mk' (CFSG.pCore 2 ↥V)), hQ.1,
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _), ?_, ?_⟩
  · intro a haA h1
    have hsq1 : a * a = 1 := Subtype.ext (S.sq_A haA)
    have h2 := hQ.2 a (sec414_isPGroup_zpowers hsq1) h1
    exact Subtype.ext (M.inf_W S haA ((sec414_mem_pCore_iff a).1 h2))
  · intro y hy1 hπ
    exact (sec414_mem_pCore_iff y).1 (hQ.2 y (sec414_isPGroup_zpowers hy1) hπ)

end CFSG.RankThree.GF2n.Tim77
