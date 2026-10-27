module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86PresWords
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Amalgam

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Quasithin CFSG.CosetTable

section Families

variable {H : Type*} [Group H]

@[expose] def linkA (w za : H) (y z : Fin 5 → H) : Fin 13 → H :=
  ![y 0, w, y 3 * y 4 * z 3, z 0 * z 4 * (z 2 * za), z 0, y 0 * (w ^ 2 * za) * y 0, w ^ 2 * za,
    z 0 * z 1, z 0 * z 1 * (y 2 * z 2), y 2 * z 2, za, z 2 * za, z 2]

@[expose] def linkB (t w1 w2 ub : H) (zm ym za : Fin 3 → H) : Fin 13 → H :=
  ![t, w1, w2, ub, zm 0, zm 1, zm 2, ym 0, ym 1, ym 2, za 0, za 1, za 2]

theorem map_linkA {K : Type*} [Group K] (f : H →* K) (w za : H) (y z : Fin 5 → H) (i : Fin 13) :
    f (linkA w za y z i) = linkA (f w) (f za) (fun j => f (y j)) (fun j => f (z j)) i := by
  fin_cases i <;> simp [linkA, map_mul, map_pow]

theorem map_linkB {K : Type*} [Group K] (f : H →* K) (t w1 w2 ub : H) (zm ym za : Fin 3 → H)
    (i : Fin 13) :
    f (linkB t w1 w2 ub zm ym za i) =
      linkB (f t) (f w1) (f w2) (f ub) (fun j => f (zm j)) (fun j => f (ym j))
        (fun j => f (za j)) i := by
  fin_cases i <;> simp [linkB]

@[expose] def linkAc (w za c : H) (y z : Fin 5 → H) : Fin 13 ⊕ Unit → H :=
  Sum.elim (linkA w za y z) fun _ => c

@[expose] def linkBc (t w1 w2 ub cb : H) (zm ym za : Fin 3 → H) : Fin 13 ⊕ Unit → H :=
  Sum.elim (linkB t w1 w2 ub zm ym za) fun _ => cb

end Families

theorem PresLinks.link {A C B : Type*} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}
    {w za : A} {y z : Fin 5 → A} {t w1 w2 ub : B} {zm ym za' : Fin 3 → B}
    (h : PresLinks X w za y z t w1 w2 ub zm ym za') (i : Fin 13) :
    AmalgamLink X (linkA w za y z i) (linkB t w1 w2 ub zm ym za' i) := by
  fin_cases i
  · exact h.lt
  · exact h.lw1
  · exact h.lw2
  · exact h.lub
  · exact h.lzm0
  · exact h.lzm1
  · exact h.lzm2
  · exact h.lym0
  · exact h.lym1
  · exact h.lym2
  · exact h.lza0
  · exact h.lza1
  · exact h.lza2

@[expose] def presLinkA : Fin 13 → PG 13 p1Words :=
  linkA (PresentedGroup.of PresP1.gw) (PresentedGroup.of PresP1.gza)
    (fun j => PresentedGroup.of (PresP1.gy j)) (fun j => PresentedGroup.of (PresP1.gz j))

@[expose] def presLinkB : Fin 13 → PG 14 p2Words :=
  linkB (PresentedGroup.of PresP2.gt) (PresentedGroup.of PresP2.gw1)
    (PresentedGroup.of PresP2.gw2) (PresentedGroup.of PresP2.gub)
    (fun i => PresentedGroup.of (PresP2.gzm i)) (fun i => PresentedGroup.of (PresP2.gym i))
    (fun i => PresentedGroup.of (PresP2.gza i))

@[expose] def presLinkAc : Fin 13 ⊕ Unit → PG 14 p1cWords :=
  linkAc (PresentedGroup.of (Fin.castSucc PresP1.gw)) (PresentedGroup.of (Fin.castSucc PresP1.gza))
    (PresentedGroup.of PresP1.gc) (fun j => PresentedGroup.of (Fin.castSucc (PresP1.gy j)))
    (fun j => PresentedGroup.of (Fin.castSucc (PresP1.gz j)))

@[expose] def presLinkBc : Fin 13 ⊕ Unit → PG 15 p2cWords :=
  linkBc (PresentedGroup.of (Fin.castSucc PresP2.gt)) (PresentedGroup.of (Fin.castSucc PresP2.gw1))
    (PresentedGroup.of (Fin.castSucc PresP2.gw2)) (PresentedGroup.of (Fin.castSucc PresP2.gub))
    (PresentedGroup.of PresP2.gc) (fun i => PresentedGroup.of (Fin.castSucc (PresP2.gzm i)))
    (fun i => PresentedGroup.of (Fin.castSucc (PresP2.gym i)))
    (fun i => PresentedGroup.of (Fin.castSucc (PresP2.gza i)))

end CFSG.Quasithin.Fan86
