module

public import CFSG.Timmesfeld.Bridge.RootStructR2ManyCore
public import CFSG.Timmesfeld.Bridge.RootStructR2Prime
public import CFSG.Timmesfeld.Bridge.RootStructWTIL2
public import CFSG.Timmesfeld.Bridge.RootSetsSyl

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

namespace RootKOne

variable {G : Type} [Group G] {D : Set G}

theorem commute_of_mem_sup {H K : Subgroup G} {g : G} (hH : ∀ u ∈ H, Commute g u)
    (hK : ∀ u ∈ K, Commute g u) {u : G} (hu : u ∈ H ⊔ K) : Commute g u := by
  have hle : H ⊔ K ≤ Subgroup.centralizer {g} :=
    sup_le (fun v hv => Subgroup.mem_centralizer_singleton_iff.2 (hH v hv).eq.symm)
      (fun v hv => Subgroup.mem_centralizer_singleton_iff.2 (hK v hv).eq.symm)
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hu)).symm

structure KOneConf (G : Type) [Group G] (D : Set G) (q : ℕ) (a x y h : G) (T₁ T₂ : Subgroup G) :
    Prop where
  counter : ThinGateCounter G D
  count : ThinGateCount G D q 1 1
  ha : a ∈ D
  hx : x ∈ D
  hy : y ∈ D
  hax : ¬ Commute a x
  hoddax : Odd (orderOf (a * x))
  hx1 : OneOpposite D a x
  hay : ¬ Commute a y
  hodday : Odd (orderOf (a * y))
  hy1 : OneOpposite D a y
  gated_x : gatedLines D a x = {T₁}
  gated_y : gatedLines D a y = {T₂}
  ne : T₁ ≠ T₂
  h_ne : h ≠ 1
  comm : ∀ u ∈ rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y, Commute h u

theorem exists_kOneConf {q : ℕ} (C : ThinGateCounter G D) (K : ThinGateCount G D q 1 1) :
    ∃ a x y h : G, ∃ T₁ T₂ : Subgroup G, KOneConf G D q a x y h T₁ T₂ := by
  have hL := RootMany.lineSetting_of_counter C
  have := C.hyp.finite
  have hD := C.hyp.root
  have hclass := C.hyp.isClass
  obtain ⟨a, ha, d, hd, had, hadD, hdT, -⟩ := hL.line
  have hq4 : 4 ≤ q := by
    rw [← K.card_rootGroup a ha]
    exact four_le_card_rootGroup hclass hD C.closure C.nontrivial ha
  obtain ⟨m, hm⟩ := exists_card_rootGroup_eq_two_pow hD ha
  rw [K.card_rootGroup a ha] at hm
  have h2q : 2 ∣ q := by
    rw [hm]
    refine dvd_pow_self 2 fun hm0 => ?_
    rw [hm0, pow_zero] at hm
    omega
  have hlines : (rootLines D a).ncard = q + 1 := by
    have h1 := K.ncard_rootLines a ha
    rwa [pow_one] at h1
  obtain ⟨T₁, hT₁def⟩ : ∃ T : Subgroup G, T = rootGroup D a ⊔ rootGroup D d := ⟨_, rfl⟩
  have hT₁ : T₁ ∈ rootLines D a := ⟨d, hd, had, hadD, hdT, hT₁def⟩
  obtain ⟨T₂, hT₂, hne⟩ := Set.exists_ne_of_one_lt_ncard (show 1 < (rootLines D a).ncard by
    omega) T₁
  obtain ⟨h₀, hh₀, hord, hh₀T₁, hh₀T₂, htrans⟩ := rootLinesTorusStep G D hL a ha d hd had hadD
    hdT (by omega) T₁ hT₁ T₂ hT₂ hne.symm
  have hord' : orderOf h₀ = q - 1 := by omega
  obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd (show q - 1 ≠ 1 by omega)
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨h, hhdef⟩ : ∃ h : G, h = h₀ ^ ((q - 1) / p) := ⟨_, rfl⟩
  have hoh : orderOf h = p := by
    rw [hhdef, ← hord']
    exact orderOf_pow_orderOf_div (by rw [hord']; omega) (by rw [hord']; exact hpq)
  have hP : IsPGroup p (Subgroup.zpowers h) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hoh, pow_one]
  have hPh : Subgroup.zpowers h ≤ Subgroup.zpowers h₀ := by
    rw [hhdef]
    exact Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers h₀) _)
  obtain ⟨x, hx, hax, hoddax, hx1, hxT₁, hxfix, -⟩ := hL.exists_fixed_of_torus C.allTI ha hd had
    hadD hdT hT₁ hT₂ hne.symm hh₀ hord hh₀T₁ hh₀T₂ htrans hp2 hP hPh
  obtain ⟨y, hy, hay, hodday, hy1, hyT₂, hyfix, -⟩ := hL.exists_fixed_of_torus C.allTI ha hd had
    hadD hdT hT₂ hT₁ hne hh₀ hord hh₀T₂ hh₀T₁
    (fun L hL₁ L' hL₂ h1 h2 h3 h4 => htrans L hL₁ L' hL₂ h2 h1 h4 h3) hp2 hP hPh
  have hgated : ∀ {z : G} {T : Subgroup G}, z ∈ D → ¬ Commute a z → Odd (orderOf (a * z)) →
      OneOpposite D a z → T ∈ gatedLines D a z → gatedLines D a z = {T} := by
    intro z T hz haz hoddaz hz1 hzT
    obtain ⟨L, hL'⟩ := Set.ncard_eq_one.1 (K.ncard_gatedLines a ha z hz haz hoddaz hz1)
    have hTL : T = L := by
      rw [hL'] at hzT
      exact Set.mem_singleton_iff.1 hzT
    rw [hL', hTL]
  have hhR : h ∈ lineGroup D a d := by
    rw [hhdef]
    exact Subgroup.pow_mem _ hh₀ _
  have hhP : h ∈ Subgroup.zpowers h := Subgroup.mem_zpowers h
  have hha : ∀ s ∈ rootGroup D a, Commute h s := fun s hs =>
    hL.commute_of_mem_lineGroup ha hd had hadD hdT hhR hs
  have hha' : ∀ a' ∈ rootSet D a, Commute h a' := fun a' ha' =>
    hha a' (rootSet_subset_rootGroup D a ha')
  have hhx : ∀ u ∈ rootGroup D x, Commute h u := fun u hu =>
    commute_of_conj_mem_rootSet_of_centralizes' C.hyp C.closure C.special ha hx hax hoddax hx1
      hha' (hxfix h hhP) hu
  have hhy : ∀ u ∈ rootGroup D y, Commute h u := fun u hu =>
    commute_of_conj_mem_rootSet_of_centralizes' C.hyp C.closure C.special ha hy hay hodday hy1
      hha' (hyfix h hhP) hu
  exact ⟨a, x, y, h, T₁, T₂,
    { counter := C
      count := K
      ha := ha
      hx := hx
      hy := hy
      hax := hax
      hoddax := hoddax
      hx1 := hx1
      hay := hay
      hodday := hodday
      hy1 := hy1
      gated_x := hgated hx hax hoddax hx1 hxT₁
      gated_y := hgated hy hay hodday hy1 hyT₂
      ne := hne.symm
      h_ne := fun h1 => hp.ne_one (by rw [← hoh, h1, orderOf_one])
      comm := fun u hu => commute_of_mem_sup (fun v hv => commute_of_mem_sup hha hhx hv) hhy hu }⟩

namespace KOneConf

variable {q : ℕ} {a x y h : G} {T₁ T₂ : Subgroup G} (K1 : KOneConf G D q a x y h T₁ T₂)
include K1

theorem a_mem_U : a ∈ rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a
    (mem_rootSet_self K1.ha)))

theorem x_mem_U : x ∈ rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_right (rootSet_subset_rootGroup D x
    (mem_rootSet_self K1.hx)))

theorem y_mem_U : y ∈ rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y :=
  Subgroup.mem_sup_right (rootSet_subset_rootGroup D y (mem_rootSet_self K1.hy))

theorem false_of_collinear {c : G} (hcD : c ∈ D)
    (hcU : c ∈ rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y) (hac : Commute a c)
    (hacD : a * c ∈ D) (hcT : c ∉ rootSet D a) : False := by
  have C := K1.counter
  have := C.hyp.finite
  have hclass := C.hyp.isClass
  have hacU := Subgroup.mul_mem _ K1.a_mem_U hcU
  have hfix : ∀ {u : G}, u ∈ rootGroup D a ⊔ rootGroup D x ⊔ rootGroup D y →
      (rootGroup D u).map (MulAut.conj h).toMonoidHom = rootGroup D u := by
    intro u hu
    rw [← rootGroup_conj hclass, (K1.comm u hu).eq, mul_inv_cancel_right]
  have hga : ∀ s ∈ rootGroup D a, Commute h s := fun s hs =>
    K1.comm s (Subgroup.mem_sup_left (Subgroup.mem_sup_left hs))
  have hua : a * c ∉ rootSet D a := fun h' => hcT (by
    have h1 : c ∈ rootGroup D a := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _
        (rootSet_subset_rootGroup D a (mem_rootSet_self K1.ha))) (rootSet_subset_rootGroup D a h')
      rwa [inv_mul_cancel_left] at this
    exact mem_rootSet_of_mem_rootGroup hclass K1.ha hcD h1)
  have huc : a * c ∉ rootSet D c := fun h' => hcT (by
    have h1 : a ∈ rootGroup D c := by
      have := Subgroup.mul_mem _ (rootSet_subset_rootGroup D c h')
        (Subgroup.inv_mem _ (rootSet_subset_rootGroup D c (mem_rootSet_self hcD)))
      rwa [mul_inv_cancel_right] at this
    exact mem_rootSet_comm hcD (mem_rootSet_of_mem_rootGroup hclass hcD K1.ha h1))
  have hAc : ∀ v ∈ rootGroup D c, Commute h v := fun v hv =>
    commute_of_map_conj_eq_of_mem_line C.hyp C.closure C.special C.allTI K1.ha hcD hacD hac hacD
      hcT (Subgroup.mul_mem _ (left_mem_line K1.ha) (right_mem_line hcD)) hua huc hga
      (hfix hcU) (hfix hacU) hv
  have hline : ∀ v ∈ rootGroup D a ⊔ rootGroup D c, Commute h v := fun v hv =>
    commute_of_mem_sup hga hAc hv
  have hcen : ∀ {z : G}, (∀ u ∈ rootGroup D z, Commute h u) →
      rootGroup D a ⊔ rootGroup D c ⊔ rootGroup D z = ⊤ → False := by
    intro z hz htop
    apply K1.h_ne
    have hmem : h ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun w => by
      have hw : w ∈ rootGroup D a ⊔ rootGroup D c ⊔ rootGroup D z := by
        rw [htop]
        exact Subgroup.mem_top w
      exact (commute_of_mem_sup hline hz hw).eq.symm
    rwa [Hyp.center_eq_bot C.hyp, Subgroup.mem_bot] at hmem
  have hLa : rootGroup D a ⊔ rootGroup D c ∈ rootLines D a := ⟨c, hcD, hac, hacD, hcT, rfl⟩
  by_cases hgx : ∃ p ∈ D, p ∈ rootGroup D a ⊔ rootGroup D c ∧ orderOf (x * p) = 4
  ·
    have h1 : rootGroup D a ⊔ rootGroup D c = T₁ := by
      have h2 : rootGroup D a ⊔ rootGroup D c ∈ gatedLines D a x := ⟨hLa, hgx⟩
      rw [K1.gated_x] at h2
      exact Set.mem_singleton_iff.1 h2
    refine hcen (z := y) (fun u hu => K1.comm u (Subgroup.mem_sup_right hu))
      (C.gen a K1.ha c hcD y K1.hy hac hacD hcT K1.hay K1.hodday K1.hy1 fun p hp hpL h4 => ?_)
    have h2 : rootGroup D a ⊔ rootGroup D c ∈ gatedLines D a y := ⟨hLa, p, hp, hpL, h4⟩
    rw [K1.gated_y, h1] at h2
    exact K1.ne (Set.mem_singleton_iff.1 h2)
  · push Not at hgx
    exact hcen (z := x) (fun u hu => K1.comm u (Subgroup.mem_sup_left (Subgroup.mem_sup_right hu)))
      (C.gen a K1.ha c hcD x K1.hx hac hacD hcT K1.hax K1.hoddax K1.hx1 hgx)

end KOneConf

end RootKOne

end CFSG.Timmesfeld.Bridge
